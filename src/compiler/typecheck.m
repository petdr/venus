%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: typecheck
% Author: peter@emailross.com
%
% Typechecking is done by converting the predicate to be typechecked into
% a set of constraints.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module typecheck.

:- interface.

:- import_module error_util.
:- import_module hlds.
:- import_module hlds_pred.

:- import_module list.

:- pred typecheck_hlds(list(error_spec)::out, hlds::in, hlds::out) is det.

:- pred typecheck_pred(hlds::in, hlds_pred::in, hlds_pred::out, list(error_spec)::out) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module hlds_goal.
:- import_module predicate_table.
:- import_module prog_data.
:- import_module prog_type.

:- import_module bimap.
:- import_module bool.
:- import_module io.
:- import_module int.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module set.
:- import_module solutions.
:- import_module svbimap.
:- import_module svmap.
:- import_module svvarset.
:- import_module term.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type typecheck_env
    --->    typecheck_env(
                pred_env    :: predicate_table
            ).

:- type typecheck_info
    --->    typecheck_info(
                % Associate a type var with a program var.
                prog_var_to_tvar    :: prog_var_to_tvar,

                % The set of all type vars
                tvarset             :: tvarset,

                % Errors encountered during type checking
                errors              :: list(error_spec)
            ).

:- type prog_var_to_tvar == bimap(prog_var, tvar).

%------------------------------------------------------------------------------%

:- type type_term == term(tvar_type).

:- type constraint
    --->    conj(list(constraint))
    ;       disj(list(constraint))
    ;       unify(tvar, type_term)
    .

:- type constraint_store == varset(tvar_type).
    
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

typecheck_hlds(Errors, !HLDS) :-
    PredIds = all_local_pred_ids(!.HLDS ^ predicate_table),
    list.foldl2(typecheck_one_pred, PredIds, [], Errors, !HLDS).
    
:- pred typecheck_one_pred(pred_id::in, list(error_spec)::in, list(error_spec)::out, hlds::in, hlds::out) is det.

typecheck_one_pred(PredId, !Errors, !HLDS) :-
    Pred0 = lookup_pred_id(!.HLDS ^ predicate_table, PredId),
    typecheck_pred(!.HLDS, Pred0, Pred, PredErrors),
    list.append(PredErrors, !Errors),
    set_hlds_pred(Pred, _PredId, !.HLDS ^ predicate_table, NewPredicateTable),
    !HLDS ^ predicate_table := NewPredicateTable.

%------------------------------------------------------------------------------%

typecheck_pred(HLDS, !Pred, Errors) :-
    some [!TCI] (
        Env = _,
        Env = init_typecheck_env(HLDS),
        !:TCI = init_typecheck_info,

        Goal = !.Pred ^ pred_goal,
        ( Goal = no_goal,
            error("XXX: there should be a goal!")
        ; Goal = goal(HldsGoal),
            goal_to_constraint(Env, HldsGoal, Constraint, !TCI),
            solutions(solve(Constraint, !.TCI ^ tvarset), Solns),
            trace [io(!IO)] (
                list.foldl(output_varset(!.TCI ^ prog_var_to_tvar, !.Pred ^ pred_varset), Solns, !IO),
                io.nl(!IO)
            )
        ),
        Errors = !.TCI ^ errors
    ).

:- pred output_varset(prog_var_to_tvar::in, prog_varset::in, tvarset::in, io::di, io::uo) is det.

output_varset(Map, ProgVarset, TVarset, !IO) :-
    io.write_string("*** Solution ***\n", !IO),
    list.foldl(output_var(Map, ProgVarset, TVarset), varset.vars(TVarset), !IO).

:- pred output_var(prog_var_to_tvar::in, prog_varset::in, tvarset::in, tvar::in, io::di, io::uo) is det.

output_var(Map, ProgVarset, TVarset, TVar, !IO) :-
    ( varset.search_var(TVarset, TVar, TypeTerm0) ->
        apply_rec_substitution(TypeTerm0, TVarset, TypeTerm),

        ( bimap.search(Map, ProgVar, TVar) ->
            io.write_string(varset.lookup_name(ProgVarset, ProgVar), !IO)
        ;
            io.write_string(varset.lookup_name(TVarset, TVar), !IO)
        ),
        io.write_string(" => ", !IO),
        ( type_term_to_prog_type(TypeTerm, Type) ->
            io.write(Type, !IO)
        ; type_term_to_prog_type_list(TypeTerm, TypeList) ->
            io.write(TypeList, !IO)
        ;
            io.write_string("unknown", !IO)
        ),
        io.nl(!IO)
    ;
        true
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func init_typecheck_info = typecheck_info.

init_typecheck_info = typecheck_info(bimap.init, varset.init, []).

:- func init_typecheck_env(hlds) = typecheck_env.

init_typecheck_env(HLDS) = typecheck_env(HLDS ^ predicate_table).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred goal_to_constraint(typecheck_env::in, hlds_goal::in, constraint::out,
    typecheck_info::in, typecheck_info::out) is det.

goal_to_constraint(Env, unify(VarA, RHS), Constraint, !TCI) :-
    get_var_type(VarA, TVarA, !TCI),
    ( RHS = rhs_var(VarB),
        get_var_type(VarB, TVarB, !TCI),
        Constraint = unify(TVarA, var(TVarB))

    ; RHS = rhs_functor(ConsId, Args),
        ( ConsId = int_const(_),
            Constraint = unify(TVarA, int)

        ; ConsId = float_const(_),
            Constraint = unify(TVarA, float)

        ; ConsId = cons(SymName),
            list.map_foldl(get_var_type, Args, ArgTVars, !TCI),
            ( SymName = sym_name([], "") ->
                ( ArgTVars = [HOCallTVar | HOArgTVars] ->
                    svvarset.new_var(ArgListVar, !.TCI ^ tvarset, TVarset),
                    !TCI ^ tvarset := TVarset,
                    C1 = unify(TVarA, functor("pred", [var(ArgListVar)])),
                    C2 = unify(HOCallTVar, functor("pred", [list(HOArgTVars, ArgListVar)])),
                    Constraint = conj([C1, C2])
                ;
                    error("XXX: no higher order argument")
                )
            ;
                    % Create a disjunction of all of the possible higher order types.
                PredTable = Env ^ pred_env,
                PredIds = search_name(PredTable, SymName),
                list.filter_map_foldl(ho_pred_unif_constraint(PredTable, TVarA, ArgTVars), PredIds, PredConstraints, !TCI),
                Constraint = maybe_to_disj(PredConstraints)
            )
        )
    ).
goal_to_constraint(Env, call(Name, Args), Constraint, !TCI) :-
    list.map_foldl(get_var_type, Args, ArgTVars, !TCI),
    ( Name = sym_name([], "") ->
        
        % Higher order call
        ( ArgTVars = [],
            error("XXX: no higher order argument")
        ; ArgTVars = [HOCallTVar | HOArgTVars],
            Constraint = unify(HOCallTVar, pred_typevars(HOArgTVars))
        )
    ;
        PredTable = Env ^ pred_env,
        PredIds = search_name_arity(PredTable, Name, list.length(Args)),
        list.map_foldl(pred_call_constraint(PredTable, ArgTVars), PredIds, PredConstraints, !TCI),
        Constraint = maybe_to_disj(PredConstraints)
    ).
goal_to_constraint(Env, conj(Goals), conj(Constraints), !TCI) :-
    list.map_foldl(goal_to_constraint(Env), Goals, Constraints, !TCI).
goal_to_constraint(_Env, method_call(_Var, _Name, _Args, _MaybeRet), disj([]), !TCI) :-
    % XXX FIXME
    error("XXX: method_call").

:- func maybe_to_disj(list(constraint)) = constraint.

maybe_to_disj(Constraints) =
    ( Constraints = [Constraint] ->
        Constraint
    ;
        disj(Constraints)
    ).

%------------------------------------------------------------------------------%

:- pred ho_pred_unif_constraint(predicate_table::in, tvar::in, list(tvar)::in, pred_id::in, constraint::out,
    typecheck_info::in, typecheck_info::out) is semidet.

ho_pred_unif_constraint(PredTable, LHSTVar, ArgTVars, PredId, Constraint, !TCI) :-
    Pred = lookup_pred_id(PredTable, PredId),

    pred_renamed_apart_argtypes(Pred, !.TCI ^ tvarset, NewTVarset, PredArgTypes),
    !TCI ^ tvarset := NewTVarset,

    ( list.split_list(list.length(ArgTVars), PredArgTypes, HOArgTypes, LambdaTypes) ->
        ArgConstraints = list.map_corresponding(unify_constraint, ArgTVars, HOArgTypes),
        LHSConstraint = unify(LHSTVar, pred_types(LambdaTypes)),
        Constraint = conj([LHSConstraint | ArgConstraints])
    ;
        % Arity less than arguments supplied
        fail
    ).

%------------------------------------------------------------------------------%

:- pred pred_call_constraint(predicate_table::in, list(tvar)::in, pred_id::in,
    constraint::out, typecheck_info::in, typecheck_info::out) is det.

pred_call_constraint(PredTable, ArgTVars, PredId, Constraint, !TCI) :-
    Pred = lookup_pred_id(PredTable, PredId),

    pred_renamed_apart_argtypes(Pred, !.TCI ^ tvarset, NewTVarset, ArgTypes),
    !TCI ^ tvarset := NewTVarset,

    % XXX
    ( list.length(ArgTypes) = Pred ^ pred_arity ->
        true
    ;
        error("XXX handle the case where we don't a pred decl for the predicate")
    ),

    Constraints = list.map_corresponding(unify_constraint, ArgTVars, ArgTypes),
    Constraint = conj(Constraints).

:- func unify_constraint(tvar, prog_type) = constraint.

unify_constraint(TVar, Type) = unify(TVar, prog_type_to_type_term(Type)).

%------------------------------------------------------------------------------%

    % If a program variable corresponds to a particular type variable, return
    % that type variable. Otherwise, create a new type variable and map the
    % program variable to it, then return that type variable.
    %
:- pred get_var_type(prog_var::in, tvar::out, typecheck_info::in, typecheck_info::out) is det.

get_var_type(Var, TVar, !TCI) :-
    ( bimap.search(!.TCI ^ prog_var_to_tvar, Var, TVar0) ->
        TVar = TVar0
    ;
        svvarset.new_var(TVar, !.TCI ^ tvarset, TVarset),
        !TCI ^ tvarset := TVarset,
        svbimap.det_insert(Var, TVar, !.TCI ^ prog_var_to_tvar, ProgVarToTVar),
        !TCI ^ prog_var_to_tvar := ProgVarToTVar
    ).

:- func prog_type_to_type_term(prog_type) = type_term.

prog_type_to_type_term(atomic_type(atomic_type_int)) = int.
prog_type_to_type_term(atomic_type(atomic_type_float)) = float.
prog_type_to_type_term(type_variable(Var)) = var(Var).
prog_type_to_type_term(higher_order_type(Args)) = pred_types(Args).

:- func pred_typevars(list(tvar)) = type_term.

pred_typevars(TVars) = functor("pred", [list(list.map(var, TVars))]).

:- func pred_types(list(prog_type)) = type_term.

pred_types(Types) = functor("pred", [list(list.map(prog_type_to_type_term, Types))]).

:- func int = type_term.

int = functor("int", []).

:- func float = type_term.

float = functor("float", []).

:- func list(list(term(T))) = term(T).

list([]) = functor("[]", []).
list([T | Ts]) = functor("[|]", [T, list(Ts)]).

:- func list(list(var(T)), var(T)) = term(T).

list([], Var) = var(Var).
list([T | Ts], Var) = functor("[|]", [var(T), list(Ts, Var)]).

:- func var(var(T)) = term(T).

var(Var) = term.variable(Var, context_init).

:- func functor(string, list(term(T))) = term(T).

functor(Functor, Args) = term.functor(atom(Functor), Args, context_init).

%------------------------------------------------------------------------------%

:- pred type_term_to_prog_type_list(type_term::in, list(prog_type)::out) is semidet.

type_term_to_prog_type_list(functor(atom("[]"), [], _), []).
type_term_to_prog_type_list(functor(atom("[|]"), [Head, Tail], _), [Type | Types]) :-
    type_term_to_prog_type(Head, Type),
    type_term_to_prog_type_list(Tail, Types).
    
:- pred type_term_to_prog_type(type_term::in, prog_type::out) is semidet.

type_term_to_prog_type(term.variable(TVar, _), type_variable(TVar)).
type_term_to_prog_type(term.functor(atom(Atom), Args, _), Type) :-
    ( Atom = "pred", Args = [Arg] ->
        type_term_to_prog_type_list(Arg, Types),
        Type = higher_order_type(Types)
    ; Atom = "int", Args = [] ->
        Type = atomic_type(atomic_type_int)
    ; Atom = "float", Args = [] ->
        Type = atomic_type(atomic_type_float)
    ;
        fail
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred solve(constraint::in, constraint_store::in, constraint_store::out) is nondet.

solve(conj([]), !Store).
solve(conj([C | Cs]), !Store) :-
    solve(C, !Store),
    solve(conj(Cs), !Store).
solve(disj([D | Ds]), !Store) :-
    (
        solve(D, !Store)
    ;
        solve(disj(Ds), !Store)
    ).
solve(unify(Var, Term), !Store) :-
    unify(variable(Var, context_init), Term, !Store).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred unify(term(T)::in, term(T)::in, varset(T)::in, varset(T)::out) is semidet.

unify(TermA, TermB, !Varset) :-
    unify_term(TermA, TermB, varset.get_bindings(!.Varset), Bindings),
    varset.set_bindings(!.Varset, Bindings, !:Varset).

:- pred apply_rec_substitution(term(T)::in, varset(T)::in, term(T)::out) is det.

apply_rec_substitution(Term0, Varset, Term) :-
    apply_rec_substitution(Term0, varset.get_bindings(Varset), Term).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
