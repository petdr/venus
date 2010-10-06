%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Venus distribution.
%------------------------------------------------------------------------------%
:- module chr.
:- interface.

:- import_module list.
:- import_module term.
:- import_module varset.

    % This is the CLP goal that we we will attempt to solve.
:- type chr_goal(T)
    --->    conj(list(chr_goal(T)))
    ;       disj(list(chr_goal(T)))
    ;       builtin(builtin_constraint(T))
    ;       chr(chr_constraint(T))
    .

    % solve(Rules, Varset, Goal, Constraints) 
    %
    % returns the set of constraints that are entailed by solving the Goal with the associated
    % CHR rules.  The varset is the varset associated with the goal.
    %
:- pred solve(list(chr_rule(T))::in, varset(T)::in, chr_goal(T)::in, list(constraint(T))::out) is nondet.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Describe CHR rules

:- type chr_rules(T) == list(chr_rule(T)).

    % chr_rule(Name, Prop, Simp, Guard, Body)
    % represents the following CHR rule
    %   Name @ Prop / Simp <=> Guard | Body.
    %
:- type chr_rule(T)
    --->    chr_rule(
                chr_name    :: chr_name,
                chr_prop    :: chr_constraints(T),
                chr_simp    :: chr_constraints(T),
                chr_guard   :: builtin_constraints(T),
                chr_body    :: constraints(T),
                chr_varset  :: varset(T)
            ).

:- type chr_name
    --->    name(string)
    ;       no_name
    .

    % A constraint is either a CHR constraint
    % or a builtin constraint.
    %
:- type constraints(T) == list(constraint(T)).
:- type constraint(T)
    --->    chr(chr_constraint(T))
    ;       builtin(builtin_constraint(T))
    .

    %
    % A CHR constraint consists of a name
    % plus a set of herbrand terms for arguments
    %
:- type chr_constraints(T) == list(chr_constraint(T)).
:- type chr_constraint(T)
    --->    chr(
                string,
                list(term(T))
            ).

    %
    % The builtin constraints supported by the system.
    % Currently only herbrand constraints are supported.
    %
:- type builtin_constraints(T) == list(builtin_constraint(T)).
:- type builtin_constraint(T)
    --->    unify(term(T), term(T))
    ;       true
    ;       fail
    .

%------------------------------------------------------------------------------%

:- type chr_goal == chr_goal(generic).
:- type chr_rule == chr_rule(generic).
:- type constraint == constraint(generic).
:- type chr_constraint == chr_constraint(generic).
:- type builtin_constraint == builtin_constraint(generic).

:- type chr_rules == chr_rules(generic).
:- type constraints == constraints(generic).
:- type chr_constraints == chr_constraints(generic).
:- type builtin_constraints == builtin_constraints(generic).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module chr_io.

:- import_module int.
:- import_module map.
:- import_module require.
:- import_module set.
:- import_module svmap.
:- import_module svset.
:- import_module svvarset.

    % The chr_program contains a representation of the
    % rules in a compiled form that are easier to use
    % during interpretation.
    %
:- type chr_program(T)
    --->    program(
                occurences              :: occurences(T),
                number_of_head_atoms    :: int
            ).

:- type occurences(T) == map(int, occurence(T)).

    % An occurence records all the information needed to fire the active
    % constraint.
    %
:- type occurence(T)
    --->    occ(
                    % The active constraint
                occ_active  :: chr_constraint(T),

                    % Do we keep or delete the active constraint
                occ_action  :: keep_or_delete,

                    % The index into the CHR rule head atoms
                occ_index   :: int,

                    % The propagation constraints
                    % which are not the active constraint.
                occ_prop    :: chr_constraints(T),

                    % The simplification constraints
                    % which are not the active constraint.
                occ_simp    :: chr_constraints(T),

                    % The guard of the rule
                occ_guard   :: builtin_constraints(T),

                    % The body of the rules
                occ_body    :: constraints(T),

                    % The varset associated with all the terms
                occ_varset  :: varset(T),
                    
                    % An id which uniquely identifies the rule
                occ_rule    :: rule_id
            ).

    % Do we keep or delete the active constraint
    % from the chr_store?
:- type keep_or_delete
    --->    keep
    ;       delete
    .

:- type rule_id ---> rule_id(int).

:- type constraint_store(T)
    --->    constraint_store(
                    % The execution stack
                a   :: list(execution(T)),
                    
                    % The store of CHR constraints
                s   :: chr_store(T),

                    % The store which holds the builtin constraints
                b   :: varset(T),

                    % The propogation history
                t   :: set(list(int)),
                    
                    % The next available identifier
                n   :: int
            ).

:- type chr_store(T) == list(chr_store_elem(T)).

    % The execution stack consists of standard constraints,
    % inactive CHR constraints and CHR constraints.
:- type execution(T)
    --->    constraint(constraint(T))
    ;       inactive(chr_constraint(T), int)
    ;       active(chr_constraint(T), int, int)
    .

    % The CHR store consists of numbered CHR constraints.
:- type chr_store_elem(T)
    --->    numbered(chr_constraint(T), int)
    .

solve(Rules, Varset0, Goal, BuiltinConstraints ++ CHRConstraints) :-
    create_chr_program(Rules, Program),
    solve_2(Program, Goal, constraint_store([], [], Varset0, set.init, 1), constraint_store(_, ChrStore, Varset, _, _)),

        % XXX it would be nice to do more simplification
    list.filter_map(to_constraint(Varset), varset.vars(Varset), BuiltinConstraints),
    CHRConstraints = list.map(func(numbered(C, _)) = chr(C), ChrStore).

:- pred to_constraint(varset(T)::in, var(T)::in, constraint(T)::out) is semidet.

to_constraint(Varset, Var, builtin(unify(variable(Var, context_init), Term))) :-
    varset.search_var(Varset, Var, Term0),
    apply_rec_substitution(Term0, varset.get_bindings(Varset), Term).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred create_chr_program(list(chr_rule(T))::in, chr_program(T)::out) is det.

create_chr_program(Rules, program(Occurences, NumberOfHeadAtoms)) :-
    list.foldl3(add_occurences, list.map(normalize_rule, Rules), 0, NumberOfHeadAtoms, 0, _NumRules, map.init, Occurences).

:- pred add_occurences(chr_rule(T)::in, int::in, int::out, int::in, int::out, occurences(T)::in, occurences(T)::out) is det.

add_occurences(Rule, !NumHeadAtoms, RuleNumber, RuleNumber + 1, !Occurences) :-
    RuleId = rule_id(RuleNumber),
    list.foldl2(add_simp_occurence(RuleId, Rule), Rule ^ chr_simp, !NumHeadAtoms, !Occurences),
    list.foldl2(add_prop_occurence(RuleId, Rule), Rule ^ chr_prop, !NumHeadAtoms, !Occurences).

:- pred add_simp_occurence(rule_id::in, chr_rule(T)::in, chr_constraint(T)::in, 
    int::in, int::out, occurences(T)::in, occurences(T)::out) is det.

add_simp_occurence(RuleId, Rule, SimpConstraint, NumHeadAtoms, Index, !Occurences) :-
    Index = NumHeadAtoms + 1,
    ( list.delete_first(Rule ^ chr_simp, SimpConstraint, Simp) ->
        Occ = occ(SimpConstraint, delete, Index, Rule ^ chr_prop, Simp, Rule ^ chr_guard, Rule ^ chr_body, Rule ^ chr_varset, RuleId),
        svmap.set(Index, Occ, !Occurences)
    ;
        error("add_simp_occurence: unable to find constraint")
    ).

:- pred add_prop_occurence(rule_id::in, chr_rule(T)::in, chr_constraint(T)::in, 
    int::in, int::out, occurences(T)::in, occurences(T)::out) is det.

add_prop_occurence(RuleId, Rule, PropConstraint, NumHeadAtoms, Index, !Occurences) :-
    Index = NumHeadAtoms + 1,
    ( list.delete_first(Rule ^ chr_prop, PropConstraint, Prop) ->
        Occ = occ(PropConstraint, keep, Index, Prop, Rule ^ chr_simp, Rule ^ chr_guard, Rule ^ chr_body, Rule ^ chr_varset, RuleId),
        svmap.set(Index, Occ, !Occurences)
    ;
        error("add_prop_occurence: unable to find constraint")
    ).

    % Normalize rule takes the head atoms of each rule and makes each head atom consist of unique variables.
    % This implies that new builtin constraints are added to the guard to model the relationship between
    % the head variables.
    %
    % This is done to make matching a lot easier.
    % 
:- func normalize_rule(chr_rule(T)) = chr_rule(T).

normalize_rule(Rule0) = Rule :-
    some [!Guard, !Varset, !SeenVars] (
        !:Guard = Rule0 ^ chr_guard,
        !:Varset = Rule0 ^ chr_varset,
        !:SeenVars = set.init,

        list.map_foldl3(normalize_constraint, Rule0 ^ chr_prop, Prop, !Guard, !Varset, !SeenVars),
        list.map_foldl3(normalize_constraint, Rule0 ^ chr_simp, Simp, !Guard, !Varset, !.SeenVars, _),

        Rule = (((Rule0
            ^ chr_prop := Prop)
            ^ chr_simp := Simp)
            ^ chr_guard := !.Guard)
            ^ chr_varset := !.Varset
    ).

:- pred normalize_constraint(chr_constraint(T)::in, chr_constraint(T)::out,
    builtin_constraints(T)::in, builtin_constraints(T)::out, varset(T)::in, varset(T)::out,
    set(var(T))::in, set(var(T))::out) is det.

normalize_constraint(chr(Name, !.Args), chr(Name, !:Args), !Guard, !Varset, !SeenVars) :-
    list.map_foldl3(normalize_chr_arg, !Args, !Guard, !Varset, !SeenVars).
    
:- pred normalize_chr_arg(term(T)::in, term(T)::out,
    builtin_constraints(T)::in, builtin_constraints(T)::out, varset(T)::in, varset(T)::out,
    set(var(T))::in, set(var(T))::out) is det.

normalize_chr_arg(Term0 @ variable(Var, Context), Term, !Guard, !Varset, !SeenVars) :-
    ( set.member(Var, !.SeenVars) ->
        svvarset.new_var(NewVar, !Varset),
        Term = variable(NewVar, Context),

        list.cons(unify(Term, Term0), !Guard),

        svset.insert(NewVar, !SeenVars)
    ;
        Term = Term0,
        svset.insert(Var, !SeenVars)
    ).
normalize_chr_arg(Term0 @ functor(_, _, _), Term, !Guard, !Varset, !SeenVars) :-
    svvarset.new_var(NewVar, !Varset),
    Term = variable(NewVar, context_init),

    list.cons(unify(Term, Term0), !Guard),

    svset.insert(NewVar, !SeenVars).
    
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

    % solve_2 implements the search part of solving the constraints.
    % The search is standard prolog depth-first search.
:- pred solve_2(chr_program(T)::in, chr_goal(T)::in, constraint_store(T)::in, constraint_store(T)::out) is nondet.

solve_2(_Program, conj([]), !Store).
solve_2(Program, conj([G | Gs]), !Store) :-
    solve_2(Program, G, !Store),
    solve_2(Program, conj(Gs), !Store).
solve_2(Program, disj([G | Gs]), !Store) :-
    (
        solve_2(Program, G, !Store)
    ;
        solve_2(Program, disj(Gs), !Store)
    ).
solve_2(Program, builtin(B), !Store) :-
    add_constraint(builtin(B), !Store),
    solve_chr(Program, !Store).
solve_2(Program, chr(C), !Store) :-
    add_constraint(chr(C), !Store),
    solve_chr(Program, !Store).

:- pred add_constraint(constraint(T)::in, constraint_store(T)::in, constraint_store(T)::out) is det.

add_constraint(Constraint, !Store) :-
    require(unify(!.Store ^ a, []), "add_constraint expects an empty execution stack"),
    !Store ^ a := [constraint(Constraint)].

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

    % solve_chr implements an interpreter for the refined operation semantics.
    % See "Compilation of Constraint Handling Rules" by Gregory J. Duck, section 3.3
    % for a description fo this state machine.
    %
:- pred solve_chr(chr_program(T)::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

solve_chr(Program, !Store) :-
    ( head_execution_stack(Head, !Store) ->
        ( Head = constraint(builtin(Builtin)),
            solve_step(Builtin, !Store)
        ; Head = constraint(chr(C)),
            activate_step(C, !Store)
        ; Head = inactive(Inactive, I),
            reactivate_step(Inactive, I, !Store)
        ; Head = active(Active, I, J),
            ( drop_step(Program, J, !Store) ->
                true
            ; simplify_step(Program, Active, I, J, !Store) ->
                true
            ; propagate_step(Program, Active, I, J, !Store) ->
                true
            ;
                default_step(Active, I, J, !Store)
            )
        ),
        solve_chr(Program, !Store)
    ;
        % There is nothing left on the execution stack, so we're finished.
        true
    ).

:- pred head_execution_stack(execution(T)::out, constraint_store(T)::in, constraint_store(T)::out) is semidet.

head_execution_stack(Head, !Store) :-
    !.Store ^ a = [Head | A],
    !Store ^ a := A.

    % The solve step solves the given builtin constraint.
    % If the builtin constraint modifies the builtin constraint store, we wake
    % any CHR constraints which can now fire.
    %
:- pred solve_step(builtin_constraint(T)::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

solve_step(true, !Store).
solve_step(fail, !Store) :-
    fail.
solve_step(unify(TermA, TermB), !Store) :-
    some [!Varset] (
        !:Varset = !.Store ^ b,
        unify_term(TermA, TermB, varset.get_bindings(!.Varset), Bindings),
        varset.set_bindings(!.Varset, Bindings, !:Varset),
        !Store ^ b := !.Varset
    ),
    wakeup_policy(!Store).

    % The activate step takes a CHR constraint, adds it as an active constraint to
    % the execution stack and to the CHR store.
:- pred activate_step(chr_constraint(T)::in, constraint_store(T)::in, constraint_store(T)::out) is det.

activate_step(CHR, !Store) :-
    N = !.Store ^ n,
    !Store ^ a := [active(CHR, N, 1) | !.Store ^ a],
    !Store ^ s := [numbered(CHR, N) | !.Store ^ s],
    !Store ^ n := N + 1.

    % The reactivate step takes an inactive constraint on the execution stack and 
    % activates it.
    %
:- pred reactivate_step(chr_constraint(T)::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is det.

reactivate_step(CHR, I, !Store) :-
    !Store ^ a := [active(CHR, I, 1) | !.Store ^ a].

    % All the occurences have been tried so drop the constraint.
    %
:- pred drop_step(chr_program(T)::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

drop_step(Program, J, !Store) :-
    J > Program ^ number_of_head_atoms,

        % The call to head_execution_stack has already removed the top most constraint
        % from the stack, so we have to do nothing here.
    true.

:- pred simplify_step(chr_program(T)::in,
    chr_constraint(T)::in, int::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

simplify_step(Program, ActiveConstraint, I, J, !Store) :-
    find_jth_occurence(Program, !.Store ^ b, J, delete, Occurence),
    execute_occurence(Program, ActiveConstraint, I, J, Occurence, !Store).

:- pred propagate_step(chr_program(T)::in,
    chr_constraint(T)::in, int::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

propagate_step(Program, ActiveConstraint, I, J, !Store) :-
    find_jth_occurence(Program, !.Store ^ b, J, keep, Occurence),
    execute_occurence(Program, ActiveConstraint, I, J, Occurence, !Store).

    % The default step moves the occurence.
:- pred default_step(chr_constraint(T)::in, int::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is det.

default_step(CHR, I, J, !Store) :-
    !Store ^ a := [active(CHR, I, J + 1) | !.Store ^ a].
    
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred find_jth_occurence(chr_program(T)::in, varset(T)::in, int::in, keep_or_delete::in, occurence(T)::out) is semidet.

find_jth_occurence(Program, Varset, J, Action, Occurence) :-
    Occurence0 = map.search(Program ^ occurences, J),
    Occurence0 ^ occ_action = Action,
    rename_apart_occurence(Occurence0, Occurence, Varset, _).
    
%------------------------------------------------------------------------------%

:- pred execute_occurence(chr_program(T)::in, chr_constraint(T)::in, int::in, int::in, occurence(T)::in,
    constraint_store(T)::in, constraint_store(T)::out) is semidet.

execute_occurence(_Program, ActiveConstraint, I, J, Occurence, !Store) :-

        % CHR rule execution is a committed choice non determinstic act so use
        % promise_equivalent_solutions to find the first solution which causes
        % a rule to fire.
    promise_equivalent_solutions [!:Store] (

        some [!Subst, !S] (
                % Match the active constraint in the CHR store
            match_ith_constraint(ActiveConstraint, I, !.Store ^ s, !:S),
            match(Occurence ^ occ_active, ActiveConstraint, map.init, !:Subst),

                % Match the rest of the head atoms in the CHR Store
            match_constraints(Occurence ^ occ_prop, Prop, !S, !Subst),
            match_constraints(Occurence ^ occ_simp, Simp, !S, !Subst),

                % Check that we haven't already executed this CHR rule
                % XXX this step is not necessary if Prop is the empty list
                % because the simplification will remove the atom and thus 
                % the i'th rule can never be used in a matching again.
            PropHistoryId = propagation_history_id(Occurence ^ occ_rule, I, Prop, Simp),
            not set.member(PropHistoryId, !.Store ^ t),

                % Check that the guard evaluates to true
            RenamedGuard = list.map(apply_rec_substitution_to_builtin(!.Subst), Occurence ^ occ_guard),
            check_guard(!.Store ^ b, RenamedGuard),

                % Rename the body of the rule and prepare it for addition back into the execution
                % stack.
            RenamedBody = list.map(apply_rec_substitution_to_constraint(!.Subst), Occurence ^ occ_body),
            BodyExecution = list.map(func(C) = constraint(C), RenamedBody),

            Action = Occurence ^ occ_action,
            ( Action = keep,
                    % Propagate step
                    %
                    % We keep the active constraint in the store and
                    % leave it on the execution stack to see if any other rules
                    % could fire with it.
                ToAddToStore = [numbered(ActiveConstraint, I) | Prop],
                ToAddToExecution = BodyExecution ++ [active(ActiveConstraint, I, J)]
            ; Action = delete,
                    % Simplify step
                    %
                    % We remove the active constraint from the store and
                    % don't add it back onto the execution stack because
                    % it's not in the store.
                ToAddToStore = Prop,
                ToAddToExecution = BodyExecution
            ),

            
                % Store that the rule has fired in the propogation history.
                % XXX this step is not necessary if Prop is the empty list.
                % because the simplification will remove the atom and thus 
                % the i'th rule can never be used in a matching again.
            set.insert(!.Store ^ t, PropHistoryId, NewT),
            !Store ^ t := NewT,

            !Store ^ a := ToAddToExecution ++ !.Store ^ a,
            !Store ^ s := ToAddToStore ++ !.S
        )
    ).

:- func propagation_history_id(rule_id, int, list(chr_store_elem(T)), list(chr_store_elem(T))) = list(int).

propagation_history_id(rule_id(R), I, Prop, Simp) = [R, I] ++ list.map(ToId, Prop) ++ list.map(ToId, Simp) :-
    ToId = (func(numbered(_, N)) = N).

%------------------------------------------------------------------------------%

:- pred match_ith_constraint(chr_constraint(T)::in, int::in, chr_store(T)::in, chr_store(T)::out) is semidet.

match_ith_constraint(Constraint, I, [C | Cs], RemainingStore) :-
    ( C = numbered(Constraint, I) ->
        RemainingStore = Cs
    ;
        match_ith_constraint(Constraint, I, Cs, RemainingStore0),
        RemainingStore = [C | RemainingStore0]
    ).

%------------------------------------------------------------------------------%

:- pred match_constraints(list(chr_constraint(T))::in, list(chr_store_elem(T))::out,
    chr_store(T)::in, chr_store(T)::out, substitution(T)::in, substitution(T)::out) is nondet.

match_constraints([], [], !Store, !Subst).
match_constraints([C | Cs], [E | Es], !Store, !Subst) :-
    match_constraint(C, E, !Store, !Subst),
    match_constraints(Cs, Es, !Store, !Subst).

:- pred match_constraint(chr_constraint(T)::in, chr_store_elem(T)::out,
    chr_store(T)::in, chr_store(T)::out, substitution(T)::in, substitution(T)::out) is nondet.

match_constraint(HeadAtom, Elem, !Store, !Subst) :-
    list.delete(!.Store, Elem, !:Store),
    Elem = numbered(StoreAtom, _N),
    match(HeadAtom, StoreAtom, !Subst).

:- pred match(chr_constraint(T)::in, chr_constraint(T)::in, substitution(T)::in, substitution(T)::out) is semidet.

match(chr(HeadName, HeadArgs), chr(StoreName, StoreArgs), !Subst) :-
    HeadName = StoreName,
    list.length(HeadArgs) : int = list.length(StoreArgs),
    list.foldl_corresponding(match_head_to_store, HeadArgs, StoreArgs, !Subst).

:- pred match_head_to_store(term(T)::in, term(T)::in, substitution(T)::in, substitution(T)::out) is det.

match_head_to_store(HeadTerm, StoreTerm, !Subst) :-
    ( HeadTerm = variable(HeadVar, _) ->
        ( svmap.insert(HeadVar, StoreTerm, !Subst) ->
            true
        ;
            error("match_head_to_store: rule normalization implies that the head variable is unique")
        )
    ;
        error("match_head_to_store: rule normalization implies that the head term is always a variable")
    ).

%------------------------------------------------------------------------------%

:- pred check_guard(varset(T)::in, builtin_constraints(T)::in) is semidet.

check_guard(_Varset, []).
check_guard(Varset, [C | Cs]) :-
    check_guard_2(Varset, C),
    check_guard(Varset, Cs).

:- pred check_guard_2(varset(T)::in, builtin_constraint(T)::in) is semidet.

check_guard_2(_, true) :-
    true.
check_guard_2(_, fail) :-
    fail.
check_guard_2(Varset, unify(TermA0, TermB0)) :-
    apply_rec_substitution(TermA0, varset.get_bindings(Varset), TermA),
    apply_rec_substitution(TermB0, varset.get_bindings(Varset), TermB),
        % XXX pretty sure that this is wrong!
    TermA = TermB.

%------------------------------------------------------------------------------%

:- pred rename_apart_occurence(occurence(T)::in, occurence(T)::out, varset(T)::in, varset(T)::out) is det.

rename_apart_occurence(!Occurence, !Varset) :-
    varset.merge_subst(!.Varset, !.Occurence ^ occ_varset, !:Varset, Subst),
    apply_substitution_to_occurence(Subst, !Occurence).

%------------------------------------------------------------------------------%

:- pred apply_substitution_to_occurence(substitution(T)::in, occurence(T)::in, occurence(T)::out) is det.

apply_substitution_to_occurence(Subst, Occurence, RenamedOccurence) :-
    apply_ho_substitution_to_occurence(apply_substitution, Subst, Occurence, RenamedOccurence).

:- func apply_substitution_to_constraint(substitution(T), constraint(T)) = constraint(T).

apply_substitution_to_constraint(Subst, C) =
    apply_ho_substitution_to_constraint(apply_substitution, Subst, C).

:- func apply_substitution_to_chr(substitution(T), chr_constraint(T)) = chr_constraint(T).

apply_substitution_to_chr(Subst, C) =
    apply_ho_substitution_to_chr(apply_substitution, Subst, C).

:- func apply_substitution_to_builtin(substitution(T), builtin_constraint(T)) = builtin_constraint(T).

apply_substitution_to_builtin(Subst, C) =
    apply_ho_substitution_to_builtin(apply_substitution, Subst, C).

%------------------------------------------------------------------------------%

:- pred apply_rec_substitution_to_occurence(substitution(T)::in, occurence(T)::in, occurence(T)::out) is det.

apply_rec_substitution_to_occurence(Subst, Occurence, RenamedOccurence) :-
    apply_ho_substitution_to_occurence(apply_rec_substitution, Subst, Occurence, RenamedOccurence).

:- func apply_rec_substitution_to_constraint(substitution(T), constraint(T)) = constraint(T).

apply_rec_substitution_to_constraint(Subst, C) =
    apply_ho_substitution_to_constraint(apply_rec_substitution, Subst, C).

:- func apply_rec_substitution_to_chr(substitution(T), chr_constraint(T)) = chr_constraint(T).

apply_rec_substitution_to_chr(Subst, C) =
    apply_ho_substitution_to_chr(apply_rec_substitution, Subst, C).

:- func apply_rec_substitution_to_builtin(substitution(T), builtin_constraint(T)) = builtin_constraint(T).

apply_rec_substitution_to_builtin(Subst, C) =
    apply_ho_substitution_to_builtin(apply_rec_substitution, Subst, C).

%------------------------------------------------------------------------------%

:- type subst_func(T) == (func(term(T), substitution(T)) = term(T)).

:- pred apply_ho_substitution_to_occurence(subst_func(T)::in, substitution(T)::in, occurence(T)::in, occurence(T)::out) is det.

apply_ho_substitution_to_occurence(F, Subst, Occurence, RenamedOccurence) :-
    RenamedOccurence = ((((Occurence
        ^ occ_active := apply_ho_substitution_to_chr(F, Subst, Occurence ^ occ_active))
        ^ occ_prop := list.map(apply_ho_substitution_to_chr(F, Subst), Occurence ^ occ_prop))
        ^ occ_simp := list.map(apply_ho_substitution_to_chr(F, Subst), Occurence ^ occ_simp))
        ^ occ_guard := list.map(apply_ho_substitution_to_builtin(F, Subst), Occurence ^ occ_guard))
        ^ occ_body := list.map(apply_ho_substitution_to_constraint(F, Subst), Occurence ^ occ_body).


:- func apply_ho_substitution_to_constraint(subst_func(T), substitution(T), constraint(T)) = constraint(T).

apply_ho_substitution_to_constraint(F, Subst, chr(Chr)) = chr(apply_ho_substitution_to_chr(F, Subst, Chr)).
apply_ho_substitution_to_constraint(F, Subst, builtin(B)) = builtin(apply_ho_substitution_to_builtin(F, Subst, B)).

:- func apply_ho_substitution_to_chr(subst_func(T), substitution(T), chr_constraint(T)) = chr_constraint(T).

apply_ho_substitution_to_chr(F, Subst, chr(Name, Args)) = chr(Name, list.map(func(Arg) = F(Arg, Subst), Args)).

:- func apply_ho_substitution_to_builtin(subst_func(T), substitution(T), builtin_constraint(T)) = builtin_constraint(T).

apply_ho_substitution_to_builtin(_, _, true) = true.
apply_ho_substitution_to_builtin(_, _, fail) = fail.
apply_ho_substitution_to_builtin(F, Subst, unify(TermA, TermB)) =
    unify(F(TermA, Subst), F(TermB, Subst)).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
    
    % Wakeup all non-fixed CHR constraints in the store and move
    % them to the head of the execution list.
:- pred wakeup_policy(constraint_store(T)::in, constraint_store(T)::out) is det.

wakeup_policy(!Store) :-
    list.filter_map(wakeup(!.Store ^ b), !.Store ^ s, ToAddToExecution),
    list.append(ToAddToExecution, !.Store ^ a, NewA),
    !Store ^ a := NewA.

    % We wakeup the chr_constraint if it contains at least one variable
    % in its args.
:- pred wakeup(varset(T)::in, chr_store_elem(T)::in, execution(T)::out) is semidet.

wakeup(Varset, Elem, Wakeup) :-
    Elem = numbered(ChrConstraint, N),
    ChrConstraint = chr(_Name, Args),
    not list.all_true(is_ground_in_bindings(get_bindings(Varset)), Args),
    Wakeup = inactive(ChrConstraint, N).

:- pred is_ground_in_bindings(substitution(T)::in, term(T)::in) is semidet.

is_ground_in_bindings(Subst, Term) :-
    is_ground_in_bindings(Term, Subst).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func chr_goal_vars(chr_goal(T)) = set(var(T)).

chr_goal_vars(conj(Gs)) = set.union_list(list.map(chr_goal_vars, Gs)).
chr_goal_vars(disj(Gs)) = set.union_list(list.map(chr_goal_vars, Gs)).
chr_goal_vars(builtin(unify(TermA, TermB))) = set(vars(TermA)) `set.union` set(vars(TermB)).
chr_goal_vars(builtin(true)) = set.init.
chr_goal_vars(builtin(fail)) = set.init.
chr_goal_vars(chr(chr(_, Terms))) = set(list.condense(list.map(vars, Terms))).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Some utility routines for debugging the CHR constraints.

:- import_module chr_io.
:- import_module io.

:- pred output_execution_stack(varset(T)::in, list(execution(T))::in, io::di, io::uo) is det.

output_execution_stack(Varset, List, !IO) :-
    io.write_string("[", !IO),
    io.write_list(List, ", ", output_execution(Varset), !IO),
    io.write_string("]", !IO).

:- pred output_execution(varset(T)::in, execution(T)::in, io::di, io::uo) is det.

output_execution(Varset, constraint(C), !IO) :-
    output_constraint(Varset, C, !IO).
output_execution(Varset, inactive(C, I), !IO) :-
    output_chr_constraint(Varset, C, !IO),
    io.write_string("#", !IO),
    io.write_int(I, !IO).
output_execution(Varset, active(C, I, J), !IO) :-
    output_execution(Varset, inactive(C, I), !IO),
    io.write_string(":", !IO),
    io.write_int(J, !IO).

:- pred output_chr_store(varset(T)::in, chr_store(T)::in, io::di, io::uo) is det.

output_chr_store(Varset, List, !IO) :-
    io.write_string("[", !IO),
    io.write_list(List, ", ", output_chr_store_elem(Varset), !IO),
    io.write_string("]", !IO).

:- pred output_chr_store_elem(varset(T)::in, chr_store_elem(T)::in, io::di, io::uo) is det.

output_chr_store_elem(Varset, numbered(C, I), !IO) :-
    output_execution(Varset, inactive(C, I), !IO).

:- pred output_chr_constraint(varset(T)::in, chr_constraint(T)::in, io::di, io::uo) is det.

output_chr_constraint(Varset, C, !IO) :-
    output_constraint(Varset, chr(C), !IO).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
