%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: predicate_table
% Author: peter@emailross.com
%
% The table which contains all the predicates in a module.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module predicate_table.

:- interface.

:- import_module hlds.
:- import_module hlds_pred.
:- import_module prog_data.

:- type predicate_table.

:- func predicate_table_init = predicate_table.

%------------------------------------------------------------------------------%

    % Add the hlds_pred to the predicate_table.
    % If the pred_id is set to invalid_pred_id then the next available
    % pred_id will be assigned to the hlds_pred before it's inserted
    % into the predicate_table.
    %
:- pred set_hlds_pred(hlds_pred::in, pred_id::out, predicate_table::in, predicate_table::out) is det.

%------------------------------------------------------------------------------%

:- pred search_pred_id(predicate_table::in, pred_id::in, hlds_pred::out) is semidet.

:- pred search_name_arity(predicate_table::in, sym_name::in, arity::in, hlds_pred::out) is semidet.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module map.
:- import_module require.

:- type predicate_table
    --->    pred_table(
                next_pred_id        :: int,
                predicates          :: map(pred_id, hlds_pred),

                % Indexes
                name_arity_index    :: map({sym_name, arity}, pred_id)
            ).

%------------------------------------------------------------------------------%

predicate_table_init = pred_table(1, map.init, map.init).

%------------------------------------------------------------------------------%

set_hlds_pred(Pred0, PredId, !PredTable) :-
    ( Pred0 ^ pred_id = invalid_pred_id ->
        next_pred_id(PredId, !PredTable),
        Pred = Pred0 ^ pred_id := PredId,

        Name = Pred ^ pred_name,
        Arity = Pred ^ pred_arity,

        !PredTable ^ predicates := map.det_insert(!.PredTable ^ predicates, PredId, Pred),
        !PredTable ^ name_arity_index := map.det_insert(!.PredTable ^ name_arity_index, {Name, Arity}, PredId)
    ;
        PredId = Pred0 ^ pred_id,
        !PredTable ^ predicates := map.det_update(!.PredTable ^ predicates, PredId, Pred0)
    ).

%------------------------------------------------------------------------------%

search_pred_id(PredTable, PredId, Pred) :-
    map.search(PredTable ^ predicates, PredId, Pred).

search_name_arity(PredTable, Name, Arity, Pred) :-
    map.search(PredTable ^ name_arity_index, {Name, Arity}, PredId),
    search_pred_id(PredTable, PredId, Pred).

%------------------------------------------------------------------------------%

:- pred next_pred_id(pred_id::out, predicate_table::in, predicate_table::out) is det.

next_pred_id(pred_id(PredId), !PredTable) :-
    PredId = !.PredTable ^ next_pred_id,
    !PredTable ^ next_pred_id := PredId + 1.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
