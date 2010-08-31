:- module prog_item.

:- interface.

:- import_module prog_data.

:- import_module list.

:- type item
    --->    clause(item_clause)
    .

:- type item_clause
    --->    clause(
                clause_name     :: string,
                clause_vars     :: list(prog_term),
                clause_goal     :: goal,
                clause_varset   :: prog_varset
            ).

:- type goal
    --->    conj(goal, goal)
    ;       unify(prog_term, prog_term)
    ;       call(string, list(prog_term))
    .

:- implementation.
