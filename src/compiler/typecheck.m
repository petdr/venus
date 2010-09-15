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
:- import_module svbimap.
:- import_module svmap.
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
                simple_constraints  :: list(simple_type_constraint),
                constraint_activity :: constraint_activity
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
                constraints         :: constraints,

                % Which constraints mention the given type var
                tvar_constraints    :: tvar_constraints,

                % Associate a type var with a program var.
                prog_var_to_tvar    :: prog_var_to_tvar,

                % Next id 
                next_constraint_id  :: int,

                % The set of all type vars
                tvarset             :: tvarset,

                % Errors encountered during type checking
                errors              :: list(error_spec)
            ).

:- type constraints == map(type_constraint_id, type_constraint).
:- type tvar_constraints == map(tvar, set(type_constraint_id)).
:- type prog_var_to_tvar == bimap(prog_var, tvar).

%------------------------------------------------------------------------------%

:- type tvar_domains == map(tvar, domain).

:- type domain
    --->    domain_any
    ;       domain_set(set(prog_type))
    ;       domain_singleton(prog_type)
    ;       domain_empty
    .

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
            goal_to_constraints(Env, HldsGoal, !TCI),
            InitDomains = map.init,
            InitLabelling = map.init,
            solve_constraints_with_labelling(!.TCI ^ tvarset, !.TCI ^ tvar_constraints, !.TCI ^ constraints, InitDomains, InitLabelling, Solution),
            trace [io(!IO)] (
                io.write(Solution, !IO),
                io.nl(!IO)
            )
        ),

        Errors = !.TCI ^ errors
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func init_typecheck_info = typecheck_info.

init_typecheck_info = typecheck_info(map.init, map.init, bimap.init, 0, varset.init, []).

:- func init_typecheck_env(hlds) = typecheck_env
init_typecheck_env(HLDS) = typecheck_env(HLDS ^ predicate_table).

%------------------------------------------------------------------------------%
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

%------------------------------------------------------------------------------%

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

:- func tvar_to_type(tvar) = prog_type.

tvar_to_type(TVar) = type_variable(TVar).

%------------------------------------------------------------------------------%

:- pred add_type_constraints(list(conj_constraints)::in, list(tvar)::in, typecheck_info::in, typecheck_info::out) is det.

add_type_constraints([], _TVars, !TCI).
add_type_constraints(Constraints @ [Single | Rest], TVars, !TCI) :-
    ( Rest = [],
        TypeConstraint = tc_conj(Single)
    ; Rest = [_|_],
        TypeConstraint = tc_disj(Constraints, no)
    ),

    next_type_constraint_id(TypeConstraintId, !TCI),
    !TCI ^ constraints := map.set(!.TCI ^ constraints, TypeConstraintId, TypeConstraint),

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
    !TCI ^ tvar_constraints := map.set(!.TCI ^ tvar_constraints, TVar, Set).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type labelling == tvar_domains.

:- type solution
    --->    solution(
                soln_domains        :: list(tvar_domains),
                soln_constraints    :: constraints,
                soln_succeeded      :: bool
            ).
                
:- pred solve_constraints_with_labelling(tvarset::in, tvar_constraints::in,
    constraints::in, tvar_domains::in, labelling::in, solution::out) is det.

solve_constraints_with_labelling(TVarset, TVarConstraints, !.Constraints, !.Domains, Labelling, Solution) :-
    !:Domains = map.union(domain_intersect, Labelling, !.Domains),
    solve_constraints(TVarset, TVarConstraints, !Constraints, !Domains),
    ( constraint_has_no_solutions(!.Domains) ->
        SolnDomains = [!.Domains],
        SolnConstraints = !.Constraints,
        SolnSucceeded = no
    ; constraint_has_multiple_solutions(!.Domains, TVar, TVarDomains) ->
        NewLabellings = list.map(map.set(Labelling, TVar), TVarDomains),
        list.map(solve_constraints_with_labelling(TVarset, TVarConstraints, !.Constraints, !.Domains), NewLabellings, Solutions),
        list.filter(solution_is_valid, Solutions, ValidSolutions, InvalidSolutions),
        ( ValidSolutions = [],
            merge_solutions(InvalidSolutions, SolnDomains, SolnConstraints),
            SolnSucceeded = no
        ; ValidSolutions = [_|_],
            merge_solutions(ValidSolutions, SolnDomains, SolnConstraints),
            SolnSucceeded = yes
        )
    ;
        SolnDomains = [!.Domains],
        SolnConstraints = !.Constraints,
        SolnSucceeded = yes
    ),
    Solution = solution(SolnDomains, SolnConstraints, SolnSucceeded).

:- pred merge_solutions(list(solution)::in, list(tvar_domains)::out, constraints::out) is det.

merge_solutions(Solutions, Domains, Constraints) :-
    Domains = list.condense(list.map(func(S) = S ^ soln_domains, Solutions)),
    RelevantConstraints = list.map(func(S) = S ^ soln_constraints, Solutions),
    ( RelevantConstraints = [],
        Constraints = map.init
    ; RelevantConstraints = [R | Rs],
        Constraints = list.foldl(map.union(merge_type_constraints), Rs, R)
    ).

    % Merges two type constraints, which should be equal except possibly
    % for the activity of their disjuncts, into one type constraint. The
    % disjuncts of the result constraint are active if the respective
    % disjuncts of either input constraint are active.
    %
:- func merge_type_constraints(type_constraint, type_constraint) = type_constraint.

merge_type_constraints(A, B) = Result :-
    (
        A = tc_conj(ConjA),
        ConjsA = [ConjA]
    ;
        A = tc_disj(ConjsA, _)
    ),
    (
        B = tc_conj(ConjB),
        ConjsB = [ConjB]
    ;
        B = tc_disj(ConjsB, _)
    ),
    Conjs = list.map_corresponding(merge_type_constraints2, ConjsA, ConjsB),
    ( Conjs = [SingletonConj] ->
        Result = tc_conj(SingletonConj)
    ; list.filter(constraint_is_active, Conjs, [SingletonConj]) ->
        Result = tc_disj(Conjs, yes(SingletonConj))
    ;
        Result = tc_disj(Conjs, no)
    ).

:- func merge_type_constraints2(conj_constraints, conj_constraints) = conj_constraints.

merge_type_constraints2(A, B) =
    (
        A ^ constraint_activity = unsatisfiable,
        B ^ constraint_activity = unsatisfiable
    ->
        A
    ;
        A ^ constraint_activity := active
    ).
    
:- pred constraint_has_multiple_solutions(tvar_domains::in, tvar::out, list(domain)::out) is semidet.

constraint_has_multiple_solutions(TVarDomains, TVar, Domains) :-
    Result = map.foldl(smallest_domain, TVarDomains, no),
    Result = yes({_, TVar, Set}),
    Domains = list.map(func(T) = domain_singleton(T), set.to_sorted_list(Set)).

:- type smallest_domain == maybe({int, tvar, set(prog_type)}).

:- func smallest_domain(tvar, domain, smallest_domain) = smallest_domain.

smallest_domain(TVar, Domain, MaybeSmallest0) = MaybeSmallest :-
    ( Domain = domain_set(Set) ->
        Size = set.count(Set),
        ( MaybeSmallest0 = no,
            MaybeSmallest = yes({Size, TVar, Set})
        ; MaybeSmallest0 = yes({SmallestSize, _, _}),
            ( Size < SmallestSize ->
                MaybeSmallest = yes({Size, TVar, Set})
            ;
                MaybeSmallest = MaybeSmallest0
            )
        )
    ;
        MaybeSmallest = MaybeSmallest0
    ).

:- pred solution_is_valid(solution::in) is semidet.

solution_is_valid(Solution) :-
    Solution ^ soln_succeeded = yes.

:- pred solve_constraints(tvarset::in, tvar_constraints::in,
    constraints::in, constraints::out, tvar_domains::in, tvar_domains::out) is det.

solve_constraints(TVarset, TVarConstraints, !Constraints, !Domains) :-
    InitialConstraints = !.Constraints,
    InitialDomains = !.Domains,
    
    ConstraintIds = map.keys(InitialConstraints),
    list.filter(has_singleton_domain(!.Domains), varset.vars(TVarset), SingletonVars),
    list.foldl3(propagate(TVarset, TVarConstraints), ConstraintIds, !Constraints, !Domains, set(SingletonVars), _),
    (
        % Failure.
        constraint_has_no_solutions(!.Domains)
    ->
        true
    ;
        % Fixed-point reached (success).
        !.Constraints = InitialConstraints,
        !.Domains = InitialDomains
    ->
        true
    ;
        % Need to iterate again.
        solve_constraints(TVarset, TVarConstraints, !Constraints, !Domains)
    ).
    

:- pred constraint_has_no_solutions(tvar_domains::in) is semidet.

constraint_has_no_solutions(Domains) :-
    list.member(domain_empty, map.values(Domains)).

:- pred propagate(tvarset::in, tvar_constraints::in, type_constraint_id::in,
    constraints::in, constraints::out, tvar_domains::in, tvar_domains::out, set(tvar)::in, set(tvar)::out) is det.

propagate(TVarset, TVarConstraints, ConstraintId, !Constraints, !Domains, !PropagatedTVars) :-
        % Update the domain of each variable in the constraint
    map.lookup(!.Constraints, ConstraintId, Constraint0),
    find_domain(Constraint0, Constraint, !Domains),
    svmap.det_update(ConstraintId, Constraint, !Constraints),
    
        % Do propagation on every TVar with a singleton domain, which hasn't
        % already been used to do propogation.
    TVars = tvars_in_constraint(Constraint),
    list.filter(has_singleton_domain(!.Domains), TVars, SingletonVars),
    ToPropagateVars = set(SingletonVars) `set.difference` !.PropagatedTVars,
    list.filter_map(map.search(TVarConstraints), set.to_sorted_list(ToPropagateVars), PropConstraints0),
    PropConstraints = set.to_sorted_list(set.union_list(PropConstraints0)),

    !:PropagatedTVars = set(SingletonVars),
    list.foldl3(propagate(TVarset, TVarConstraints), PropConstraints, !Constraints, !Domains, !PropagatedTVars).

:- pred has_singleton_domain(tvar_domains::in, tvar::in)  is semidet.

has_singleton_domain(Domains, TVar) :-
    Domain = tvar_domain(Domains, TVar),
    Domain = domain_singleton(_).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

    %
    % find_domain(!Constraint, !Domains)
    %
    % Given !.Constraint update the !Domains using the constraints.
    % !:Constraint will be the constraint after marking it's individual components unsatisfiable or active.
    %
:- pred find_domain(type_constraint::in, type_constraint::out, tvar_domains::in, tvar_domains::out) is det.

find_domain(tc_conj(!.ConjConstraints), tc_conj(!:ConjConstraints), !Domains) :-
    find_domain_of_conj_constraints(!ConjConstraints, !Domains).
find_domain(tc_disj(DisjConstraints, yes(!.Single)), tc_disj(DisjConstraints, yes(!:Single)), !Domains) :-
    find_domain_of_conj_constraints(!Single, !Domains).
find_domain(tc_disj(!.DisjConstraints, no), tc_disj(!:DisjConstraints, MaybeSingle), !Domains) :-
        % For each of the active constraints create the domain for that
        % constraint starting from the initial domain.
    list.filter(constraint_is_active, !DisjConstraints, InvalidConstraints),
    list.map2(create_domain(!.Domains), !DisjConstraints, DisjDomainsList),

        % The domain of all of the disjunctions is the union of all of the active
        % arms of the the disjunction.
    ( DisjDomainsList = [],
        DisjDomain = map.init
    ; DisjDomainsList = [HeadDomain | TailDomains],
        DisjDomain = list.foldl(map.intersect(domain_union), TailDomains, HeadDomain)
    ),

        % Now apply the disjunctions domain to the current domain
    !:Domains = map.union(domain_intersect, DisjDomain, !.Domains),

        % Determine if there is only one constraint active and 
        % if so record it.
    list.filter(constraint_is_active, !.DisjConstraints, Active),
    ( Active = [Single] ->
        MaybeSingle = yes(Single)
    ;
        MaybeSingle = no
    ),

        % Add back in the invalid constraints.
    list.append(!.DisjConstraints, InvalidConstraints, !:DisjConstraints).

%------------------------------------------------------------------------------%

:- pred create_domain(tvar_domains::in, conj_constraints::in, conj_constraints::out, tvar_domains::out) is det.

create_domain(!.Domains, !ConjConstraints, !:Domains) :-
    find_domain_of_conj_constraints(!ConjConstraints, !Domains).

%------------------------------------------------------------------------------%
    
    %
    % Find the domain of a conjunction of constraints.
    %
:- pred find_domain_of_conj_constraints(conj_constraints::in, conj_constraints::out,
    tvar_domains::in, tvar_domains::out) is det.

find_domain_of_conj_constraints(!ConjConstraints, !Domains) :-
    ( !.ConjConstraints = conj_constraints(_, unsatisfiable),
        true
    ; !.ConjConstraints = conj_constraints(SimpleConstraints, active),
        InitialDomains = !.Domains,
        list.foldl(find_domain_of_simple_type_constraint, SimpleConstraints, !Domains),
        ( simple_constaints_are_satisfiable(!.Domains, SimpleConstraints) ->
            ( domains_unchanged(!.Domains, InitialDomains) ->
                true
            ;
                find_domain_of_conj_constraints(!ConjConstraints, !Domains)
            )
        ;
            !ConjConstraints ^ constraint_activity := unsatisfiable
        )
    ).

%------------------------------------------------------------------------------%

:- pred find_domain_of_simple_type_constraint(simple_type_constraint::in, tvar_domains::in, tvar_domains::out) is det.

find_domain_of_simple_type_constraint(simple(TVarA, type_variable(TVarB)), !Domains) :-
        % The domain of each type variable is the intersection
        % of the two type variables domains.
    DomainA = tvar_domain(!.Domains, TVarA),
    DomainB = tvar_domain(!.Domains, TVarB),
    Domain = domain_intersect(DomainA, DomainB),
    svmap.det_update(TVarA, Domain, !Domains),
    svmap.det_update(TVarB, Domain, !Domains).

find_domain_of_simple_type_constraint(simple(TVarA, TypeA @ atomic_type(_)), !Domains) :-
        % Restrict the domain of the type variable to be that of the atomic type.
    restrict_domain(TVarA, TypeA, !Domains).

find_domain_of_simple_type_constraint(simple(TVarA, higher_order_type(Args0)), !Domains) :-
        % For each type variable in the higher_order_type if that type variable
        % has a singleton type then get it, then use these argument types
        % to restrict the domain of the type variable.
    Args = list.map(find_type_of_tvar(!.Domains), Args0),
    restrict_domain(TVarA, higher_order_type(Args), !Domains).

:- func find_type_of_tvar(tvar_domains, prog_type) = prog_type.

find_type_of_tvar(Domains, Type) =
    (
        Type = type_variable(TVar),
        map.search(Domains, TVar, domain_singleton(TVarType))
    ->
        TVarType
    ;
        Type
    ).

%------------------------------------------------------------------------------%

:- pred constraint_is_active(conj_constraints::in) is semidet.

constraint_is_active(ConjConstraints) :-
    ConjConstraints ^ constraint_activity = active.

:- pred simple_constaints_are_satisfiable(tvar_domains::in, list(simple_type_constraint)::in) is semidet.

simple_constaints_are_satisfiable(Domains, SimpleConstraints) :-
    TVars = list.condense(list.map(tvars_in_simple_constraint, SimpleConstraints)),
    DomainsList = list.map(tvar_domain(Domains), TVars),
    list.all_true(non_empty_domain, DomainsList).

:- pred non_empty_domain(domain::in) is semidet.

non_empty_domain(Domain) :-
    Domain \= domain_empty.

%------------------------------------------------------------------------------%

:- func tvars_in_constraint(type_constraint) = list(tvar).

tvars_in_constraint(TypeConstraint) = list.condense(list.map(tvars_in_simple_constraint, Simple)) :-
    ( TypeConstraint = tc_conj(ConjConstraints),
        Simple = ConjConstraints ^ simple_constraints
    ; TypeConstraint = tc_disj(ConjConstraintsList, _),
        Simple = list.condense(list.map(func(C) = C ^ simple_constraints, ConjConstraintsList))
    ).

:- func tvars_in_simple_constraint(simple_type_constraint) = list(tvar).

tvars_in_simple_constraint(simple(TVar, Type)) = [TVar | type_vars(Type)].

%------------------------------------------------------------------------------%

:- pred domains_unchanged(tvar_domains::in, tvar_domains::in) is semidet.

domains_unchanged(DomainsA, DomainsB) :-
    TVars = list.sort_and_remove_dups(map.keys(DomainsA) ++ map.keys(DomainsB)),
    domains_unchanged_2(TVars, DomainsA, DomainsB).

:- pred domains_unchanged_2(list(tvar)::in, tvar_domains::in, tvar_domains::in) is semidet.

domains_unchanged_2([], _, _).
domains_unchanged_2([TVar | TVars], DomainsA, DomainsB) :-
    equal_domains(tvar_domain(DomainsA, TVar), tvar_domain(DomainsB, TVar)),
    domains_unchanged_2(TVars, DomainsA, DomainsB).

:- pred equal_domains(domain::in, domain::in) is semidet.

equal_domains(domain_any, domain_any).
equal_domains(domain_set(SetA), domain_set(SetB)) :-
    list.map_corresponding(unify_types, to_sorted_list(SetA), to_sorted_list(SetB), _).
equal_domains(domain_singleton(TypeA), domain_singleton(TypeB)) :-
    unify_types(TypeA, TypeB, _).
equal_domains(domain_empty, domain_empty).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

    %
    % Restrict the domain of the given tvar to the prog_type in the tvar_domains map.
    %
:- pred restrict_domain(tvar::in, prog_type::in, tvar_domains::in, tvar_domains::out) is det.

restrict_domain(TVar, Type, !Domains) :-
    Domain = domain_intersect(tvar_domain(!.Domains, TVar), domain_singleton(Type)),
    svmap.set(TVar, Domain, !Domains).

    %
    % Find the union of two domains
    %
:- func domain_union(domain, domain) = domain.

domain_union(domain_any, _) = domain_any.

domain_union(domain_set(_), domain_any) = domain_any.
domain_union(domain_set(SetA), domain_set(SetB)) = domain_set(SetA `set.union` SetB).
domain_union(domain_set(SetA), domain_singleton(TypeB)) = domain_set(set.insert(SetA, TypeB)).
domain_union(domain_set(SetA), domain_empty) = domain_set(SetA).

domain_union(domain_singleton(_), domain_any) = domain_any.
domain_union(domain_singleton(TypeA), domain_set(SetB)) = domain_set(set.insert(SetB, TypeA)).
domain_union(domain_singleton(TypeA), domain_singleton(TypeB)) = normalize_domain(domain_set(set([TypeA, TypeB]))).
domain_union(domain_singleton(TypeA), domain_empty) = domain_singleton(TypeA).

domain_union(domain_empty, DomainB) = DomainB.

    %
    % Find the intersection of two domains
    %
:- func domain_intersect(domain, domain) = domain.

domain_intersect(domain_any, DomainB) = DomainB.

domain_intersect(DomainA @ domain_set(_), domain_any) = DomainA.
domain_intersect(domain_set(SetA), domain_set(SetB)) = normalize_domain(Domain) :-
    ListA = set.to_sorted_list(SetA),
    ListB = set.to_sorted_list(SetB),
    List = domain_list_intersect(ListA, ListB),
    Domain = domain_set(set(List)).
domain_intersect(DomainA @ domain_set(_), domain_singleton(TypeB)) =
    domain_intersect(DomainA, domain_set(set([TypeB]))).
domain_intersect(domain_set(_), domain_empty) = domain_empty.

domain_intersect(DomainA @ domain_singleton(_), domain_any) = DomainA.
domain_intersect(domain_singleton(TypeA), DomainB @ domain_set(_)) =
    domain_intersect(domain_set(set([TypeA])), DomainB).
domain_intersect(domain_singleton(TypeA), domain_singleton(TypeB)) =
    ( unify_types(TypeA, TypeB, TypeAB) ->
        domain_singleton(TypeAB)
    ;
        domain_empty
    ).
domain_intersect(domain_singleton(_), domain_empty) = domain_empty.

domain_intersect(domain_empty, _) = domain_empty.

    % The intersection of two lists of prog_types
    % Note the lists have to be sorted.
    %
:- func domain_list_intersect(list(prog_type), list(prog_type)) = list(prog_type).

domain_list_intersect([], _) = [].
domain_list_intersect([_|_], []) = [].
domain_list_intersect([A | As], [B | Bs]) = Cs :-
    ( unify_types(A, B, AB) ->
        Cs = [AB | domain_list_intersect(As, Bs)]
    ;
        compare(R, A, B),
        ( R = (<),
            Cs = domain_list_intersect(As, [B | Bs])
        ; R = (=),
            Cs = domain_list_intersect(As, Bs)
        ; R = (>),
            Cs = domain_list_intersect([A | As], Bs)
        )
    ).

    % Find the most general unifier of two types.
:- pred unify_types(prog_type::in, prog_type::in, prog_type::out) is semidet.

unify_types(TypeA, TypeB, Type) :-
    ( TypeB = type_variable(_) ->
        Type = TypeA
    ; TypeA = type_variable(_) ->
        Type = TypeB
    ;
        (
            TypeA = atomic_type(Atomic),
            TypeB = atomic_type(Atomic),
            Type = TypeA
        ;
            TypeA = higher_order_type(ArgsA),
            TypeB = higher_order_type(ArgsB),
            list.map_corresponding(unify_types, ArgsA, ArgsB, Args),
            Type = higher_order_type(Args)
        )
    ).

:- func normalize_domain(domain) = domain.

normalize_domain(domain_any) = domain_any.
normalize_domain(domain_set(Types)) =
    ( set.empty(Types) ->
        domain_empty
    ; set.singleton_set(Types, Type) ->
        domain_singleton(Type)
    ;
        domain_set(Types)
    ).
normalize_domain(domain_singleton(Type)) = domain_singleton(Type).
normalize_domain(domain_empty) = domain_empty.

:- func tvar_domain(tvar_domains, tvar) = domain.

tvar_domain(Domains, TVar) =
    ( map.search(Domains, TVar, Domain) ->
        Domain
    ;
        domain_any
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
