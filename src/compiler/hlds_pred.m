%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: hlds_pred
% Author: peter@emailross.com
%
% Representation of HLDS predicates.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module hlds_pred.
:- interface.

:- import_module hlds.
:- import_module hlds_goal.
:- import_module prog_data.

:- import_module list.

:- type pred_id
    --->    pred_id(int).

:- type hlds_pred
    --->    hlds_pred(
                pred_id         :: pred_id,
                pred_name       :: sym_name,
                pred_arity      :: arity,
                pred_status     :: import_status,
                pred_args       :: list(prog_var),
                pred_tvarset    :: tvarset,
                pred_varset     :: prog_varset,
                pred_goal       :: pred_goal
            ).

:- type pred_goal
    --->    no_goal
    ;       goal(hlds_goal)     % This is the goal before type checking
    .

:- func invalid_pred_id = pred_id.

:- implementation.

invalid_pred_id = pred_id(-1).
