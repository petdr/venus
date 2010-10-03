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
                chr_body    :: constraints(T)
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

:- import_module require.
:- import_module set.

:- type chr_program(T)
    --->    program(list(chr_rule(T))).

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
    solve_2(program(Rules), Goal, constraint_store([], [], Varset0, set.init, 1), constraint_store(_, _, Varset, _, _)),

        % XXX it would be nice to do more simplification
    list.filter_map(to_constraint(Varset), varset.vars(Varset), Constraints).

:- pred to_constraint(varset(T)::in, var(T)::in, constraint(T)::out) is semidet.

to_constraint(Varset, Var, builtin(unify(variable(Var, context_init), Term))) :-
    varset.search_var(Varset, Var, Term0),
    apply_rec_substitution(Term0, varset.get_bindings(Varset), Term).

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

solve_chr(_Program, !Store) :-
    ( head_execution_stack(Head, !Store) ->
        ( Head = constraint(builtin(Builtin)),
            % SOLVE
            solve_step(Builtin, !Store)
        ; Head = constraint(chr(_CHR)),
            % ACTIVATE
            fail
        ; Head = inactive(_CHR, _I),
            % REACTIVATE
            fail
        ; Head = active(_CHR, _I, _J),
            % DROP
            % SIMPLIFY
            % PROPAGATE
            % DEFAULT
            fail
        )
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
