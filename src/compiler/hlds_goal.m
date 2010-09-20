%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
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

:- import_module index.
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
    ;       disj(
                disj_goals  :: list(hlds_goal)
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
    --->    cons(sym_name, arity)
    ;       int_const(int)
    ;       float_const(float)
    .

:- instance index_key(cons_id).

:- implementation.

:- instance index_key(cons_id) where [
    (smaller_key(cons(!.SymName, Arity), cons(!:SymName, Arity)) :-
        smaller_key(!SymName)
    )
].
