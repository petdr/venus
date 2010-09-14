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
                pred_varset     :: prog_varset,
                pred_types      :: list(prog_type),
                pred_tvarset    :: tvarset,
                pred_goal       :: pred_goal
            ).

:- type pred_goal
    --->    no_goal
    ;       goal(hlds_goal)     % This is the goal before type checking
    .

:- func invalid_pred_id = pred_id.

    %
    % pred_renamed_apart_args(Pred, TVarset0, TVarset, Args)
    %
    % Return the arguments types such that each type variable in Args is renamed apart from type variables
    % in TVarset0.
    %
:- pred pred_renamed_apart_args(hlds_pred::in, tvarset::in, tvarset::out, list(prog_type)::out) is det.


:- implementation.

:- import_module map.

invalid_pred_id = pred_id(-1).

pred_renamed_apart_args(Pred, !TVarset, Args) :-
    tvarset_merge_renaming(!.TVarset, Pred ^ pred_tvarset, !:TVarset, Renaming),
    Args = apply_variable_renaming_to_type_list(Renaming, Pred ^ pred_types).

:- func apply_variable_renaming_to_type_list(tvar_renaming, list(prog_type)) = list(prog_type).

apply_variable_renaming_to_type_list(Renaming, Types) =
    list.map(apply_variable_renaming_to_type(Renaming), Types).
    
:- func apply_variable_renaming_to_type(tvar_renaming, prog_type) = prog_type.

apply_variable_renaming_to_type(Renaming, Type0) = Type :-
    (
        Type0 = type_variable(TVar0),
        TVar = apply_variable_renaming_to_tvar(Renaming, TVar0),
        Type = type_variable(TVar)
    ;
        Type0 = atomic_type(_),
        Type = Type0
    ;
        Type0 = higher_order_type(Args0),
        Args = apply_variable_renaming_to_type_list(Renaming, Args0),
        Type = higher_order_type(Args)
    ).

:- func apply_variable_renaming_to_tvar(tvar_renaming, tvar) = tvar.

apply_variable_renaming_to_tvar(Renaming, TVar0) = TVar :-
    ( map.search(Renaming, TVar0, TVar1) ->
        TVar = TVar1
    ;
        TVar = TVar0
    ).
