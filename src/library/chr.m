%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Venus distribution.
%------------------------------------------------------------------------------%
:- module chr.
:- interface.

:- import_module list.
:- import_module term.
:- import_module varset.

:- type chr_goal(T)
    --->    conj(list(chr_goal(T)))
    ;       disj(list(chr_goal(T)))
    ;       builtin(builtin_constraint(T))
    ;       chr(chr_constraint(T))
    .

:- pred solve(list(chr_rule(T))::in, varset(T)::in, chr_goal(T)::in, list(constraint(T))::out) is nondet.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% Describe CHR rules

:- type chr_rules(T) == list(chr_rule(T)).
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

:- type constraints(T) == list(constraint(T)).
:- type constraint(T)
    --->    chr(chr_constraint(T))
    ;       builtin(builtin_constraint(T))
    .

:- type chr_constraints(T) == list(chr_constraint(T)).
:- type chr_constraint(T)
    --->    chr(
                string,
                list(term(T))
            ).

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

:- type chr_program(T)
    --->    program(
                occurences              :: occurences(T),
                number_of_head_atoms    :: int
            ).

:- type occurences(T) == map(int, occurence(T)).
:- type occurence(T)
    --->    occ(
                occ_active  :: chr_constraint(T),
                occ_action  :: keep_or_delete,
                occ_index   :: int,
                occ_prop    :: chr_constraints(T),
                occ_simp    :: chr_constraints(T),
                occ_guard   :: builtin_constraints(T),
                occ_varset  :: varset(T),
                occ_rule    :: int
            ).

:- type keep_or_delete
    --->    keep
    ;       delete
    .

        

:- type constraint_store(T)
    --->    constraint_store(
                a   :: list(execution(T)),
                s   :: list(chr_store_elem(T)),
                b   :: varset(T),
                t   :: set(list(int)),
                n   :: int
            ).

:- type execution(T)
    --->    constraint(constraint(T))
    ;       inactive(chr_constraint(T), int)
    ;       active(chr_constraint(T), int, int)
    .

:- type chr_store_elem(T)
    --->    numbered(chr_constraint(T), int)
    ;       normal(chr_constraint(T))
    .

solve(Rules, Varset0, Goal, Constraints) :-
    create_chr_program(Rules, Program),
    solve_2(Program, Goal, constraint_store([], [], Varset0, set.init, 1), constraint_store(_, _, Varset, _, _)),

        % XXX it would be nice to do more simplification
    list.filter_map(to_constraint(Varset), varset.vars(Varset), Constraints).

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
    list.foldl2(add_simp_occurence(RuleNumber, Rule), Rule ^ chr_simp, !NumHeadAtoms, !Occurences),
    list.foldl2(add_prop_occurence(RuleNumber, Rule), Rule ^ chr_prop, !NumHeadAtoms, !Occurences).

:- pred add_simp_occurence(int::in, chr_rule(T)::in, chr_constraint(T)::in, 
    int::in, int::out, occurences(T)::in, occurences(T)::out) is det.

add_simp_occurence(RuleNumber, Rule, SimpConstraint, NumHeadAtoms, Index, !Occurences) :-
    Index = NumHeadAtoms + 1,
    ( list.delete_first(Rule ^ chr_simp, SimpConstraint, Simp) ->
        Occ = occ(SimpConstraint, delete, Index, Rule ^ chr_prop, Simp, Rule ^ chr_guard, Rule ^ chr_varset, RuleNumber),
        svmap.set(Index, Occ, !Occurences)
    ;
        error("add_simp_occurence: unable to find constraint")
    ).

:- pred add_prop_occurence(int::in, chr_rule(T)::in, chr_constraint(T)::in, 
    int::in, int::out, occurences(T)::in, occurences(T)::out) is det.

add_prop_occurence(RuleNumber, Rule, PropConstraint, NumHeadAtoms, Index, !Occurences) :-
    Index = NumHeadAtoms + 1,
    ( list.delete_first(Rule ^ chr_prop, PropConstraint, Prop) ->
        Occ = occ(PropConstraint, keep, Index, Prop, Rule ^ chr_simp, Rule ^ chr_guard, Rule ^ chr_varset, RuleNumber),
        svmap.set(Index, Occ, !Occurences)
    ;
        error("add_prop_occurence: unable to find constraint")
    ).

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
    builtin_constraints(T)::in, builtin_constraints(T)::out, varset(T)::in, varset(T)::out, set(var(T))::in, set(var(T))::out) is det.

normalize_constraint(chr(Name, !.Args), chr(Name, !:Args), !Guard, !Varset, !SeenVars) :-
    list.map_foldl3(normalize_chr_arg, !Args, !Guard, !Varset, !SeenVars).
    
:- pred normalize_chr_arg(term(T)::in, term(T)::out,
    builtin_constraints(T)::in, builtin_constraints(T)::out, varset(T)::in, varset(T)::out, set(var(T))::in, set(var(T))::out) is det.

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

:- pred solve_chr(chr_program(T)::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

solve_chr(Program, !Store) :-
    ( head_execution_stack(Head, !Store) ->
        ( Head = constraint(builtin(Builtin)),
            solve_step(Builtin, !Store)
        ; Head = constraint(chr(CHR)),
            activate_step(CHR, !Store)
        ; Head = inactive(CHR, I),
            reactivate_step(CHR, I, !Store)
        ; Head = active(CHR, I, J),
            ( J > Program ^ number_of_head_atoms ->
                drop_step(!Store)
            ;
                % SIMPLIFY
                % PROPAGATE
                default_step(CHR, I, J, !Store)
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

:- pred activate_step(chr_constraint(T)::in, constraint_store(T)::in, constraint_store(T)::out) is det.

activate_step(CHR, !Store) :-
    N = !.Store ^ n,
    !Store ^ a := [active(CHR, N, 1) | !.Store ^ a],
    !Store ^ s := [numbered(CHR, N) | !.Store ^ s],
    !Store ^ n := N + 1.

:- pred reactivate_step(chr_constraint(T)::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is det.

reactivate_step(CHR, I, !Store) :-
    !Store ^ a := [active(CHR, I, 1) | !.Store ^ a].

:- pred drop_step(constraint_store(T)::in, constraint_store(T)::out) is det.

    % The call to head_execution_stack has already removed the top most constraint
    % from the stack, so we have to do nothing here.
drop_step(!Store).

:- pred default_step(chr_constraint(T)::in, int::in, int::in, constraint_store(T)::in, constraint_store(T)::out) is det.

default_step(CHR, I, J, !Store) :-
    !Store ^ a := [active(CHR, I, J + 1) | !.Store ^ a].

    
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred rename_apart_occurence(occurence(T)::in, occurence(T)::out, varset(T)::in, varset(T)::out) is det.

rename_apart_occurence(!Occurence, !Varset) :-
    varset.merge_subst(!.Varset, !.Occurence ^ occ_varset, !:Varset, Subst),
    apply_rec_substitution_to_occurence(Subst, !Occurence).

:- pred apply_rec_substitution_to_occurence(substitution(T)::in, occurence(T)::in, occurence(T)::out) is det.

apply_rec_substitution_to_occurence(Subst, Occurence, RenamedOccurence) :-
    RenamedOccurence = (((Occurence
        ^ occ_active := apply_rec_substitution_to_chr(Subst, Occurence ^ occ_active))
        ^ occ_prop := list.map(apply_rec_substitution_to_chr(Subst), Occurence ^ occ_prop))
        ^ occ_simp := list.map(apply_rec_substitution_to_chr(Subst), Occurence ^ occ_simp))
        ^ occ_guard := list.map(apply_rec_substitution_to_builtin(Subst), Occurence ^ occ_guard).

:- func apply_rec_substitution_to_chr(substitution(T), chr_constraint(T)) = chr_constraint(T).

apply_rec_substitution_to_chr(Subst, chr(Name, Args)) = chr(Name, apply_rec_substitution_to_list(Args, Subst)).

:- func apply_rec_substitution_to_builtin(substitution(T), builtin_constraint(T)) = builtin_constraint(T).

apply_rec_substitution_to_builtin(_, true) = true.
apply_rec_substitution_to_builtin(_, fail) = fail.
apply_rec_substitution_to_builtin(Subst, unify(TermA, TermB)) =
    unify(apply_rec_substitution(TermA, Subst), apply_rec_substitution(TermB, Subst)).


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
    ( Elem = numbered(ChrConstraint, N),
        Wakeup = inactive(ChrConstraint, N)
    ; Elem = normal(ChrConstraint),
        Wakeup = constraint(chr(ChrConstraint))
    ),
    ChrConstraint = chr(_Name, Args),
    not list.all_true(is_ground_in_bindings(get_bindings(Varset)), Args).

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
