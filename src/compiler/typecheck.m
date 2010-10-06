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

:- import_module hlds_data.
:- import_module hlds_goal.
:- import_module predicate_table.
:- import_module prog_data.
:- import_module prog_type.

:- import_module chr.
:- import_module chr_io.

:- import_module bimap.
:- import_module bool.
:- import_module index.
:- import_module int.
:- import_module io.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module set.
:- import_module solutions.
:- import_module string.
:- import_module svbimap.
:- import_module svmap.
:- import_module svvarset.
:- import_module term.
:- import_module term_io.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type typecheck_env
    --->    typecheck_env(
                func_env    :: cons_table,
                pred_env    :: predicate_table
            ).

:- type typecheck_info
    --->    typecheck_info(
                % Associate a type var with a program var.
                prog_var_to_tvar    :: prog_var_to_tvar,

                % The program variable varset
                prog_varset         :: prog_varset,

                % The set of all type vars
                tvarset             :: tvarset,

                % Errors encountered during type checking
                errors              :: list(error_spec)
            ).

:- type prog_var_to_tvar == bimap(prog_var, tvar).

%------------------------------------------------------------------------------%

:- type type_term == term(tvar_type).

:- type tconstraint == constraint(tvar_type).
:- type tchr_constraint == chr_constraint(tvar_type).
:- type tbuiltin_constraint == builtin_constraint(tvar_type).
:- type tchr_goal == chr_goal(tvar_type).
:- type tchr_rule == chr_rule(tvar_type).

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
        !:TCI = init_typecheck_info(!.Pred ^ pred_varset),

        Goal = !.Pred ^ pred_goal,
        ( Goal = no_goal,
            error("XXX: there should be a goal!")
        ; Goal = goal(HldsGoal),
            pred_renamed_apart_argtypes(!.Pred, !.TCI ^ tvarset, NewTVarset, PredArgTypes, PredUnivConstraints),
            !TCI ^ tvarset := NewTVarset,

                % Do we have a predicate declaration for the types.
            ( list.length(PredArgTypes) : int = list.length(!.Pred ^ pred_args) ->
                list.map_foldl(get_var_type, !.Pred ^ pred_args, ArgTVars, !TCI),
                TypeclassConstraints = list.map(prog_constraint_constraint, PredUnivConstraints),
                ArgConstraints = list.map_corresponding(unify_constraint, ArgTVars, PredArgTypes)
            ;
                TypeclassConstraints = [],
                ArgConstraints = []
            ),

            goal_to_constraint(Env, HldsGoal, GoalConstraint, !TCI),

                % XXX for the moment I don't think we need the typeclass constraints
            _ = TypeclassConstraints,
            Constraint = maybe_to_conj(ArgConstraints ++ [GoalConstraint]),

                % Ensure that each variable in the varset has a unique name.
                % This is so that output_constraint and output_varset are
                % comprehensible.
            TVarset0 = !.TCI ^ tvarset,
            !TCI ^ tvarset := varset.ensure_unique_names(varset.vars(TVarset0), "X", TVarset0),

            Rules = [],
            solutions(solve(Rules, !.TCI ^ tvarset, Constraint), Solns),
            trace [io(!IO)] (
                output_chr_goal(!.TCI ^ tvarset, Constraint, !IO),
                list.foldl(output_solution(!.TCI ^ tvarset), Solns, !IO),
                io.nl(!IO),
                io.nl(!IO)
            )
        ),
        Errors = !.TCI ^ errors
    ).

:- pred output_solution(varset(T)::in, list(constraint(T))::in, io::di, io::uo) is det.

output_solution(Varset, Constraints, !IO) :-
    io.write_string("\n*** Solution ***\n", !IO),
    list.foldl(output(Varset), Constraints, !IO).

:- pred output(varset(T)::in, constraint(T)::in, io::di, io::uo) is det.

output(Varset, Constraint, !IO) :-
    output_constraint(Varset, Constraint, !IO),
    io.nl(!IO).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func init_typecheck_info(prog_varset) = typecheck_info.

init_typecheck_info(ProgVarset) = typecheck_info(bimap.init, ProgVarset, varset.init, []).

:- func init_typecheck_env(hlds) = typecheck_env.

init_typecheck_env(HLDS) = typecheck_env(HLDS ^ cons_table, HLDS ^ predicate_table).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred goal_to_constraint(typecheck_env::in, hlds_goal::in, tchr_goal::out,
    typecheck_info::in, typecheck_info::out) is det.

goal_to_constraint(Env, unify(VarA, RHS), Constraint, !TCI) :-
    get_var_type(VarA, TVarA, !TCI),
    ( RHS = rhs_var(VarB),
        get_var_type(VarB, TVarB, !TCI),
        Constraint = builtin(unify(var(TVarA), var(TVarB)))

    ; RHS = rhs_functor(ConsId, Args),
        ( ConsId = int_const(_),
            Constraint = builtin(unify(var(TVarA), int))

        ; ConsId = float_const(_),
            Constraint = builtin(unify(var(TVarA), float))

        ; ConsId = cons(SymName, _Arity),
            list.map_foldl(get_var_type, Args, ArgTVars, !TCI),
            ( SymName = sym_name([], "") ->
                ( ArgTVars = [HOCallTVar | HOArgTVars] ->
                    svvarset.new_uniquely_named_var("ArgList", ArgListVar, !.TCI ^ tvarset, TVarset),
                    !TCI ^ tvarset := TVarset,
                    C1 = builtin(unify(var(TVarA), functor(ho_type_name, [var(ArgListVar)]))),
                    C2 = builtin(unify(var(HOCallTVar), functor(ho_type_name, [list(HOArgTVars, ArgListVar)]))),
                    Constraint = conj([C1, C2])
                ;
                    error("XXX: no higher order argument")
                )
            ;
                    % Lookup the cons_table to find all possible 
                ConsTable = Env ^ func_env,
                ConsDefns = index.lookup(ConsTable, ConsId),
                list.map_foldl(functor_unif_constraint(TVarA, ArgTVars), ConsDefns, DataConstraints, !TCI),

                    % Create a disjunction of all of the possible higher order types.
                PredTable = Env ^ pred_env,
                PredIds = search_name(PredTable, SymName),
                list.filter_map_foldl(ho_pred_unif_constraint(PredTable, TVarA, ArgTVars), PredIds, PredConstraints, !TCI),
                Constraint = maybe_to_disj(DataConstraints ++ PredConstraints)
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
            Constraint = builtin(unify(var(HOCallTVar), pred_typevars(HOArgTVars)))
        )
    ;
        PredTable = Env ^ pred_env,
        PredIds = search_name_arity(PredTable, Name, list.length(Args)),
        list.map_foldl(pred_call_constraint(PredTable, ArgTVars), PredIds, PredConstraints, !TCI),
        Constraint = maybe_to_disj(PredConstraints)
    ).
goal_to_constraint(Env, conj(Goals), conj(Constraints), !TCI) :-
    list.map_foldl(goal_to_constraint(Env), Goals, Constraints, !TCI).
goal_to_constraint(Env, disj(Goals), conj(Constraints), !TCI) :-
    list.map_foldl(goal_to_constraint(Env), Goals, Constraints, !TCI).
goal_to_constraint(_Env, method_call(_Var, _Name, _Args, _MaybeRet), disj([]), !TCI) :-
    % XXX FIXME
    error("XXX: method_call").

:- func maybe_to_disj(list(tchr_goal)) = tchr_goal.

maybe_to_disj(Constraints) =
    ( Constraints = [Constraint] ->
        Constraint
    ;
        disj(Constraints)
    ).

:- func maybe_to_conj(list(tchr_goal)) = tchr_goal.

maybe_to_conj(Constraints) =
    ( Constraints = [Constraint] ->
        Constraint
    ;
        conj(Constraints)
    ).

%------------------------------------------------------------------------------%

:- pred functor_unif_constraint(tvar::in, list(tvar)::in, hlds_cons_defn::in, tchr_goal::out,
    typecheck_info::in, typecheck_info::out) is det.

functor_unif_constraint(LHSTVar, ArgTVars, ConsDefn, Constraint, !TCI) :-
    tvarset_merge_renaming(!.TCI ^ tvarset, ConsDefn ^ cons_type_tvarset, NewTVarset, Renaming),
    !TCI ^ tvarset := NewTVarset,

    Args = apply_variable_renaming_to_type_list(Renaming, ConsDefn ^ cons_args),
    ArgConstraints = list.map_corresponding(unify_constraint, ArgTVars, Args),

    Params = apply_variable_renaming_to_type_list(Renaming, ConsDefn ^ cons_type_params),
    LHSConstraint = unify_constraint(LHSTVar, construct_type(ConsDefn ^ cons_type_ctor, Params)),

    Constraint = maybe_to_conj([LHSConstraint | ArgConstraints]).

:- func construct_type(type_ctor, list(prog_type)) = prog_type.

construct_type(type_ctor(Name, _), Args) = defined_type(Name, Args).

%------------------------------------------------------------------------------%

:- pred ho_pred_unif_constraint(predicate_table::in, tvar::in, list(tvar)::in, pred_id::in, tchr_goal::out,
    typecheck_info::in, typecheck_info::out) is semidet.

ho_pred_unif_constraint(PredTable, LHSTVar, ArgTVars, PredId, Constraint, !TCI) :-
    Pred = lookup_pred_id(PredTable, PredId),

    pred_renamed_apart_argtypes(Pred, !.TCI ^ tvarset, NewTVarset, PredArgTypes, PredUnivConstraints),
    !TCI ^ tvarset := NewTVarset,

    ( list.split_list(list.length(ArgTVars), PredArgTypes, HOArgTypes, LambdaTypes) ->
        TypeclassConstraints = list.map(prog_constraint_constraint, PredUnivConstraints),
        ArgConstraints = list.map_corresponding(unify_constraint, ArgTVars, HOArgTypes),
        LHSConstraint = builtin(unify(var(LHSTVar), pred_types(LambdaTypes))),
        Constraint = maybe_to_conj([LHSConstraint | ArgConstraints ++ TypeclassConstraints])
    ;
        % Arity less than arguments supplied
        fail
    ).

:- func prog_constraint_constraint(prog_constraint) = tchr_goal.

prog_constraint_constraint(prog_constraint(SymName, Args)) =
    chr(chr(sym_name_to_string(SymName), list.map(prog_type_to_type_term, Args))).

%------------------------------------------------------------------------------%

:- pred pred_call_constraint(predicate_table::in, list(tvar)::in, pred_id::in,
    tchr_goal::out, typecheck_info::in, typecheck_info::out) is det.

pred_call_constraint(PredTable, ArgTVars, PredId, Constraint, !TCI) :-
    Pred = lookup_pred_id(PredTable, PredId),

    pred_renamed_apart_argtypes(Pred, !.TCI ^ tvarset, NewTVarset, ArgTypes, UnivConstraints),
    !TCI ^ tvarset := NewTVarset,

    % XXX
    ( list.length(ArgTypes) = Pred ^ pred_arity ->
        true
    ;
        error("XXX handle the case where we don't a pred decl for the predicate")
    ),

    TypeclassConstraints = list.map(prog_constraint_constraint, UnivConstraints),
    Constraints = list.map_corresponding(unify_constraint, ArgTVars, ArgTypes),
    Constraint = maybe_to_conj(Constraints ++ TypeclassConstraints).

:- func unify_constraint(tvar, prog_type) = tchr_goal.

unify_constraint(TVar, Type) = builtin(unify(var(TVar), prog_type_to_type_term(Type))).

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
        svvarset.new_named_var(varset.lookup_name(!.TCI ^ prog_varset, Var), TVar, !.TCI ^ tvarset, TVarset),
        !TCI ^ tvarset := TVarset,
        svbimap.det_insert(Var, TVar, !.TCI ^ prog_var_to_tvar, ProgVarToTVar),
        !TCI ^ prog_var_to_tvar := ProgVarToTVar
    ).

:- func prog_type_to_type_term(prog_type) = type_term.

prog_type_to_type_term(atomic_type(atomic_type_int)) = int.
prog_type_to_type_term(atomic_type(atomic_type_float)) = float.
prog_type_to_type_term(type_variable(Var)) = var(Var).
prog_type_to_type_term(higher_order_type(Args)) = pred_types(Args).
prog_type_to_type_term(defined_type(SymName, Args)) =
    functor(sym_name_to_string(SymName), list.map(prog_type_to_type_term, Args)).

:- func sym_name_to_string(sym_name) = string.

sym_name_to_string(sym_name(Qualifiers, Name)) =
    string.append_list(list.map(func(S) = S ++ ".", Qualifiers) ++ [Name]).

:- func string_to_sym_name(string) = sym_name.

string_to_sym_name(String) = sym_name(Qualifiers, Name) :-
    L = string.split_at_string(".", String),
    ( list.split_last(L, Qualifiers0, Name0) ->
        Qualifiers = Qualifiers0,
        Name = Name0
    ;
        Qualifiers = [],
        Name = String
    ).

:- func pred_typevars(list(tvar)) = type_term.

pred_typevars(TVars) = functor(ho_type_name, [list(list.map(var, TVars))]).

:- func pred_types(list(prog_type)) = type_term.

pred_types(Types) = functor(ho_type_name, [list(list.map(prog_type_to_type_term, Types))]).

:- func ho_type_name = string.
ho_type_name = "$pred$".

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
    ( Atom = ho_type_name, Args = [Arg] ->
        type_term_to_prog_type_list(Arg, Types),
        Type = higher_order_type(Types)
    ; Atom = "int", Args = [] ->
        Type = atomic_type(atomic_type_int)
    ; Atom = "float", Args = [] ->
        Type = atomic_type(atomic_type_float)
    ;
        list.map(type_term_to_prog_type, Args, Types),
        Type = defined_type(string_to_sym_name(Atom), Types)
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

    % Take a constraint and flatten all the disjunctions and conjunctions.
:- func flatten(chr_goal(T)) = chr_goal(T).

flatten(conj(Gs)) = conj(list.reverse(list.foldl(flatten_conj, Gs, []))).
flatten(disj(Gs)) = disj(list.reverse(list.foldl(flatten_disj, Gs, []))).
flatten(C @ builtin(_)) = C.
flatten(C @ chr(_)) = C.

:- func flatten_conj(chr_goal(T), list(chr_goal(T))) = list(chr_goal(T)).

flatten_conj(C0, !.Gs) = !:Gs :-
    C = flatten(C0),
    ( C = conj(Cs) ->
        list.append(Cs, !Gs)
    ;
        list.append([C], !Gs)
    ).

:- func flatten_disj(chr_goal(T), list(chr_goal(T))) = list(chr_goal(T)).

flatten_disj(C0, !.Gs) = !:Gs :-
    C = flatten(C0),
    ( C = disj(Cs) ->
        list.append(Cs, !Gs)
    ;
        list.append([C], !Gs)
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred output_chr_goal(varset(T)::in, chr_goal(T)::in, io::di, io::uo) is det.

output_chr_goal(Varset, Constraint, !IO) :-
    io.write_string("*** Constraint ***", !IO),
    output_chr_goal_2(0, Varset, flatten(Constraint), !IO),
    io.nl(!IO).

%------------------------------------------------------------------------------%

:- pred output_chr_goal_2(int::in, varset(T)::in, chr_goal(T)::in, io::di, io::uo) is det.

output_chr_goal_2(Indent, Varset, conj(Cs), !IO) :-
    ( Cs = [],
        output_indent(Indent, !IO),
        io.write_string("true", !IO)
    ; Cs = [H | T],
        output_chr_goal_2(Indent, Varset, H, !IO),
        output_chr_goal_list(Indent, Varset, conj_sep, T, !IO)
    ).
output_chr_goal_2(Indent, Varset, disj(Cs), !IO) :-
    ( Cs = [],
        output_indent(Indent, !IO),
        io.write_string("fail", !IO)
    ; Cs = [H|T],
        output_indent(Indent, !IO),
        io.write_string("(", !IO),
        output_chr_goal_2(Indent + 1, Varset, H, !IO),
        output_chr_goal_list(Indent + 1, Varset, disj_sep, T, !IO),
        output_indent(Indent, !IO),
        io.write_string(")", !IO)
    ).
output_chr_goal_2(Indent, _Varset, builtin(fail), !IO) :-
    output_indent(Indent, !IO),
    io.write_string("true", !IO).
output_chr_goal_2(Indent, _Varset, builtin(true), !IO) :-
    output_indent(Indent, !IO),
    io.write_string("true", !IO).
output_chr_goal_2(Indent, Varset, builtin(unify(TermA, TermB)), !IO) :-
    output_indent(Indent, !IO),
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" = ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_chr_goal_2(Indent, Varset, chr(chr(Name, Args)), !IO) :-
    output_indent(Indent, !IO),
    term_io.write_term(Varset, functor(Name, Args), !IO).

%------------------------------------------------------------------------------%

:- type sep
    --->    conj_sep
    ;       disj_sep
    .

:- pred output_chr_goal_list(int::in, varset(T)::in, sep::in, list(chr_goal(T))::in, io::di, io::uo) is det.

output_chr_goal_list(_Indent, _Varset, _Sep, [], !IO).
output_chr_goal_list(Indent, Varset, Sep, [C | Cs], !IO) :-
    ( Sep = conj_sep,
        io.write_string(",", !IO)
    ; Sep = disj_sep,
        output_indent(Indent - 1, !IO),
        io.write_string(";", !IO)
    ),
    output_chr_goal_2(Indent, Varset, C, !IO),
    output_chr_goal_list(Indent, Varset, Sep, Cs, !IO).

%------------------------------------------------------------------------------%

:- pred output_indent(int::in, io::di, io::uo) is det.

output_indent(N, !IO) :-
    io.nl(!IO),
    output_indent_2(N, !IO).

:- pred output_indent_2(int::in, io::di, io::uo) is det.

output_indent_2(N, !IO) :-
    ( N > 0 ->
        io.write_string(" ", !IO),
        output_indent_2(N - 1, !IO)
    ;
        true
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
