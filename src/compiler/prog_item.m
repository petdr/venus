:- module prog_item.

:- interface.

:- import_module prog_data.

:- import_module list.

:- type item
    --->    clause(item_clause)
    .

:- type sym_name == string.

:- type item_clause
    --->    clause(
                clause_name     :: sym_name,
                clause_vars     :: list(prog_term),
                clause_goal     :: goal,
                clause_varset   :: prog_varset
            ).

:- type goal
    --->    conj(goal, goal)
    ;       unify(prog_term, prog_term)
    ;       call(string, list(prog_term))
    ;       object_void_call(object_method)
    ;       object_function_call(prog_term, object_method)
    .

:- type object_method
    --->    object_method(
                object_var      :: prog_var,
                object_method   :: sym_name,
                object_args     :: list(prog_term)
            ).
        
:- implementation.
