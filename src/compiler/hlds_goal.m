:- module hlds_goal.

:- interface.

:- import_module prog_data.

:- type hlds_goal
    --->    unify(
                unify_lhs   :: prog_var,
                unify_rhs   :: unify_rhs
            )
    ;       call(
                call_name   :: string,
                call_args   :: list(prog_var)
            )
    ;       conj(
                conj_goals  :: list(hlds_goal)
            )
    .

:- type unify_rhs
    --->    rhs_var(
                var_var         :: prog_var
            )
    ;       rhs_functor(
                functor_cons_id :: cons_id,
                functor_vars    :: list(prog_var)
            ).

:- type cons_id
    --->    cons(string)
    ;       int_const(int)
    .
