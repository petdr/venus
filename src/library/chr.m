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

    % A CHR program consists of a set of chr_rule
:- type chr_program(T).

:- type chr_rule(T)
    --->    chr_rule(
                chr_name    :: chr_name,
                chr_prop    :: list(chr_constraint(T)),
                chr_simp    :: list(chr_constraint(T)),
                chr_guard   :: list(builtin_constraint(T)),
                chr_body    :: list(constraint(T))
            ).

:- type chr_name
    --->    name(string)
    .

:- type constraint(T)
    --->    chr(chr_constraint(T))
    ;       builtin(builtin_constraint(T))
    .

:- type chr_constraint(T)
    --->    chr(
                string,
                list(term(T))
            ).

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

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module chr_io.

:- import_module set.

:- type chr_program(T)
    --->    program(list(chr_rule(T))).

:- type constraint_store(T)
    --->    constraint_store(
                varset(T)
            ).

solve(Rules, Varset0, Goal, Constraints) :-
    solve_2(program(Rules), Goal, constraint_store(Varset0), constraint_store(Varset)),

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
solve_2(_Program, builtin(unify(TermA, TermB)), !Store) :-
    add_unify_constraint(TermA, TermB, !Store).
solve_2(_Program, builtin(true), !Store).
solve_2(_Program, builtin(fail), !Store) :-
    fail.
solve_2(_Program, chr(_Constraint), !Store) :-
    % XXX fix me.
    fail.

:- pred add_unify_constraint(term(T)::in, term(T)::in, constraint_store(T)::in, constraint_store(T)::out) is semidet.

add_unify_constraint(TermA, TermB, constraint_store(!.Varset), constraint_store(!:Varset)) :-
    unify_term(TermA, TermB, varset.get_bindings(!.Varset), Bindings),
    varset.set_bindings(!.Varset, Bindings, !:Varset).

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
