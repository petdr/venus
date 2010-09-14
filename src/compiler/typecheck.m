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
:- import_module int.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module set.
:- import_module svbimap.
:- import_module svvarset.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type type_constraint_id
    --->    type_constraint_id(int).

:- type type_constraint
    --->    tc_conj(
                % A conjunction of constraints all of which must hold
                conj_constraints
            )
    ;       tc_disj(
                % A disjunction of conjunctions of constraints,
                % introduced by by ambiguity of unifications and calls
                % This is how overloading is modelled and resolved.
                list(conj_constraints),

                % yes(Conj) when propogation has reduced the disjunction
                % to a single conjunction of constraints.
                maybe(conj_constraints)
            )
    .

:- type conj_constraints
    --->    conj_constraints(
                list(simple_type_constraint),
                constraint_activity
            ).

:- type constraint_activity
    --->    active
    ;       unsatisfiable
    .

:- type simple_type_constraint
    --->    simple(
                tvar,       % The variable whose type is being constrained
                prog_type   % The type to which the variable is being assigned
            ).

%------------------------------------------------------------------------------%

:- type typecheck_env
    --->    typecheck_env(
                pred_env    :: predicate_table
            ).

:- type typecheck_info
    --->    typecheck_info(
                % All the constraints
                constraints         :: map(type_constraint_id, type_constraint),

                % Which constraints mention the given type var
                tvar_constraints    :: map(tvar, set(type_constraint_id)),

                % Associate a type var with a program var.
                typevar_map         :: bimap(prog_var, tvar),

                % Next id 
                next_constraint_id  :: int,

                % The set of all type vars
                tvarset             :: tvarset,

                % Errors encountered during type checking
                errors              :: list(error_spec)
            ).

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

typecheck_pred(HLDS, !Pred, Errors) :-
    some [!TCI] (
        Env = _,
        Env = init_typecheck_env(HLDS),
        !:TCI = init_typecheck_info,

        Goal = !.Pred ^ pred_goal,
        ( Goal = no_goal,
            error("XXX: there should be a goal!")
        ; Goal = goal(HldsGoal),
            goal_to_constraints(Env, HldsGoal, !TCI)
        ),

        Errors = !.TCI ^ errors
    ).

%------------------------------------------------------------------------------%

:- pred goal_to_constraints(typecheck_env::in, hlds_goal::in, typecheck_info::in, typecheck_info::out) is det.

goal_to_constraints(_Env, unify(VarA, RHS), !TCI) :-
    get_var_type(VarA, TVarA, !TCI),
    ( RHS = rhs_var(VarB),
        get_var_type(VarB, TVarB, !TCI),
        Constraints = [conj_constraints([simple(TVarA, tvar_to_type(TVarB))], active)],
        RelevantTVars = [TVarA, TVarB]

    ; RHS = rhs_functor(ConsId, _Args),
        ( ConsId = int_const(_),
            Constraints = [conj_constraints([simple(TVarA, atomic_type(atomic_type_int))], active)],
            RelevantTVars = [TVarA]

        ; ConsId = cons(_SymName),
            % XXX for the moment we don't handle this case!
            error("XXX: ConsId = cons(_)")
        )
    ),
    add_type_constraints(Constraints, RelevantTVars, !TCI).
goal_to_constraints(Env, call(Name, Args), !TCI) :-
    PredTable = Env ^ pred_env,
    PredIds = search_name_arity(PredTable, Name, list.length(Args)),
    list.map_foldl(get_var_type, Args, ArgTVars, !TCI),
    list.map2_foldl(pred_call_constraint(PredTable, ArgTVars), PredIds, ConjConstraintsList, PredTVarsList, !TCI),
    RelevantTVars = list.condense([ArgTVars | PredTVarsList]),
    add_type_constraints(ConjConstraintsList, RelevantTVars, !TCI).
goal_to_constraints(Env, conj(Goals), !TCI) :-
    list.foldl(goal_to_constraints(Env), Goals, !TCI).
goal_to_constraints(_Env, method_call(_Var, _Name, _Args, _MaybeRet), !TCI) :-
    % XXX FIXME
    error("XXX: method_call").

:- pred pred_call_constraint(predicate_table::in, list(tvar)::in, pred_id::in,
    conj_constraints::out, list(tvar)::out, typecheck_info::in, typecheck_info::out) is det.

pred_call_constraint(PredTable, ArgTVars, PredId, ConjConstraints, PredTVars, !TCI) :-
    Pred = lookup_pred_id(PredTable, PredId),

    pred_renamed_apart_argtypes(Pred, !.TCI ^ tvarset, NewTVarset, ArgTypes),
    !TCI ^ tvarset := NewTVarset,

    % XXX
    ( list.length(ArgTypes) = Pred ^ pred_arity ->
        true
    ;
        error("XXX handle the case where we don't a pred decl for the predicate")
    ),

    Constraints = list.map_corresponding(func(TVar, Type) = simple(TVar, Type), ArgTVars, ArgTypes),
    PredTVars = type_list_vars(ArgTypes),

    ConjConstraints = conj_constraints(Constraints, active).

:- pred add_type_constraints(list(conj_constraints)::in, list(tvar)::in, typecheck_info::in, typecheck_info::out) is det.

add_type_constraints([], _TVars, !TCI).
add_type_constraints(Constraints @ [Single | Rest], TVars, !TCI) :-
    ( Rest = [],
        TypeConstraint = tc_conj(Single)
    ; Rest = [_|_],
        TypeConstraint = tc_disj(Constraints, no)
    ),
    next_type_constraint_id(TypeConstraintId, !TCI),

    map.set(!.TCI ^ constraints, TypeConstraintId, TypeConstraint, NewConstraintsMap),
    !TCI ^ constraints := NewConstraintsMap,

    list.foldl(update_tvar_constraints(TypeConstraintId), TVars, !TCI).

:- pred next_type_constraint_id(type_constraint_id::out, typecheck_info::in, typecheck_info::out) is det.

next_type_constraint_id(type_constraint_id(Id), !TCI) :-
    Id = !.TCI ^ next_constraint_id,
    !TCI ^ next_constraint_id := Id + 1.

:- pred update_tvar_constraints(type_constraint_id::in, tvar::in, typecheck_info::in, typecheck_info::out) is det.

update_tvar_constraints(Id, TVar, !TCI) :-
    ( map.search(!.TCI ^ tvar_constraints, TVar, Set0) ->
        Set = set.insert(Set0, Id)
    ;
        Set = set([Id])
    ),
    map.set(!.TCI ^ tvar_constraints, TVar, Set, NewTvarConstraints),
    !TCI ^ tvar_constraints := NewTvarConstraints.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func init_typecheck_info = typecheck_info.

init_typecheck_info = typecheck_info(map.init, map.init, bimap.init, 0, varset.init, []).

:- func init_typecheck_env(hlds) = typecheck_env.

init_typecheck_env(HLDS) = typecheck_env(HLDS ^ predicate_table).

%------------------------------------------------------------------------------%

    % If a program variable corresponds to a particular type variable, return
    % that type variable. Otherwise, create a new type variable and map the
    % program variable to it, then return that type variable.
    %
:- pred get_var_type(prog_var::in, tvar::out, typecheck_info::in, typecheck_info::out) is det.

get_var_type(Var, TVar, !TCI) :-
    ( bimap.search(!.TCI ^ typevar_map, Var, TVar0) ->
        TVar = TVar0
    ;
        svvarset.new_var(TVar, !.TCI ^ tvarset, TVarset),
        !TCI ^ tvarset := TVarset,
        svbimap.det_insert(Var, TVar, !.TCI ^ typevar_map, TVarmap),
        !TCI ^ typevar_map := TVarmap
    ).

:- func tvar_to_type(tvar) = prog_type.

tvar_to_type(TVar) = type_variable(TVar).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
