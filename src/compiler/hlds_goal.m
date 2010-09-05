%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: hlds_goal
% Author: peter@emailross.com
%
% Representation of HLDS goals.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module hlds_goal.

:- interface.

:- import_module prog_data.

:- import_module list.
:- import_module maybe.

:- type hlds_goal
    --->    unify(
                unify_lhs   :: prog_var,
                unify_rhs   :: unify_rhs
            )
    ;       call(
                call_name   :: sym_name,
                call_args   :: list(prog_var)
            )
    ;       conj(
                conj_goals  :: list(hlds_goal)
            )
    ;       method_call(
                method_var  :: prog_var,
                method_name :: sym_name,
                method_args :: list(prog_var),
                method_ret  :: maybe(prog_var)
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
    --->    cons(sym_name)
    ;       int_const(int)
    .
