%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
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

:- import_module hlds_pred.
:- import_module prog_data.

:- import_module list.

:- type predicate_table.

:- func predicate_table_init = predicate_table.

%------------------------------------------------------------------------------%
    
    % Get all the pred_ids in the predicate_table.
:- func all_pred_ids(predicate_table) = list(pred_id).

    % Get all the pred_ids for all local predicates in the predicate table
:- func all_local_pred_ids(predicate_table) = list(pred_id).

%------------------------------------------------------------------------------%

    % Add the hlds_pred to the predicate_table.
    % If the pred_id is set to invalid_pred_id then the next available
    % pred_id will be assigned to the hlds_pred before it's inserted
    % into the predicate_table.
    %
:- pred set_hlds_pred(hlds_pred::in, pred_id::out, predicate_table::in, predicate_table::out) is det.

%------------------------------------------------------------------------------%

    % Lookup the hlds_pred associated with a sym_name and arity, throws an
    % exception if the sym_name and arity doesn't uniquely specify a predicate.
    %
:- func lookup_name_arity(predicate_table, sym_name, arity) = hlds_pred.

    % Find the hlds_pred for the given sym_name and arity.  Fails if there is more
    % than one or no hlds_pred found.
    %
:- pred search_name_arity(predicate_table::in, sym_name::in, arity::in, hlds_pred::out) is semidet.

    % Find all the pred_ids of predicates with the given sym_name and arity.
    %
:- func search_name_arity(predicate_table, sym_name, arity) = list(pred_id).

    % Find all the pred_ids of predicates with the given sym_name.
    %
:- func search_name(predicate_table, sym_name) = list(pred_id).

    %
    % Is the a hlds_pred with the given pred_id in the predicate_table.
    % lookup_pred_id throws an exception if there is no hlds_pred associated
    % with the pred_id while search_pred_id fails.
    %
:- func lookup_pred_id(predicate_table, pred_id) = hlds_pred.
:- pred search_pred_id(predicate_table::in, pred_id::in, hlds_pred::out) is semidet.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module hlds.

:- import_module int.
:- import_module map.
:- import_module multi_map.
:- import_module require.

:- type predicate_table
    --->    pred_table(
                next_pred_id        :: int,
                predicates          :: map(pred_id, hlds_pred),

                % Indexes
                name_arity_index    :: multi_map(sym_name_and_arity, pred_id),
                name_index          :: multi_map(sym_name, pred_id)
            ).

%------------------------------------------------------------------------------%

predicate_table_init = pred_table(1, map.init, map.init, map.init).

%------------------------------------------------------------------------------%

all_pred_ids(PredTable) = map.keys(PredTable ^ predicates).

all_local_pred_ids(PredTable) = LocalPredIds :-
    list.filter(
        (pred(PredId::in) is semidet :-
            Pred = lookup_pred_id(PredTable, PredId),
            Pred ^ pred_status = is_local
        ), all_pred_ids(PredTable), LocalPredIds).

%------------------------------------------------------------------------------%

set_hlds_pred(Pred0, PredId, !PredTable) :-
    ( Pred0 ^ pred_id = invalid_pred_id ->
        next_pred_id(PredId, !PredTable),
        Pred = Pred0 ^ pred_id := PredId,

        Name = Pred ^ pred_name,
        Arity = Pred ^ pred_arity,

        !PredTable ^ predicates := map.det_insert(!.PredTable ^ predicates, PredId, Pred),
        add_name_to_indices(Name, Arity, PredId, !PredTable)
    ;
        PredId = Pred0 ^ pred_id,
        !PredTable ^ predicates := map.det_update(!.PredTable ^ predicates, PredId, Pred0)
    ).

:- pred add_name_to_indices(sym_name::in, arity::in, pred_id::in, predicate_table::in, predicate_table::out) is det.

add_name_to_indices(SymName @ sym_name(ModuleName, LocalName), Arity, PredId, !PredTable) :-
    !PredTable ^ name_arity_index := multi_map.set(!.PredTable ^ name_arity_index, SymName / Arity, PredId),
    !PredTable ^ name_index := multi_map.set(!.PredTable ^ name_index, SymName, PredId),
    ( ModuleName = [],
        true
    ; ModuleName = [_ | PartiallyQualifiedModuleName],
        add_name_to_indices(sym_name(PartiallyQualifiedModuleName, LocalName), Arity, PredId, !PredTable)
    ).



%------------------------------------------------------------------------------%

lookup_name_arity(PredTable, Name, Arity) = 
    ( search_name_arity(PredTable, Name, Arity, Pred) ->
        Pred
    ;
        func_error("lookup_name_arity: distinct predicate not found!")
    ).

search_name_arity(PredTable, Name, Arity, Pred) :-
    PredIds = search_name_arity(PredTable, Name, Arity),
    PredIds = [PredId],
    search_pred_id(PredTable, PredId, Pred).

search_name_arity(PredTable, Name, Arity) = 
    ( map.search(PredTable ^ name_arity_index, Name / Arity, PredIds) ->
        PredIds
    ;
        []
    ).

search_name(PredTable, Name) = 
    ( map.search(PredTable ^ name_index, Name, PredIds) ->
        PredIds
    ;
        []
    ).

lookup_pred_id(PredTable, PredId) =
    ( search_pred_id(PredTable, PredId, Pred) ->
        Pred
    ;
        func_error("lookup_pred_id: pred_id not found")
    ).

search_pred_id(PredTable, PredId, Pred) :-
    map.search(PredTable ^ predicates, PredId, Pred).

%------------------------------------------------------------------------------%

:- pred next_pred_id(pred_id::out, predicate_table::in, predicate_table::out) is det.

next_pred_id(pred_id(PredId), !PredTable) :-
    PredId = !.PredTable ^ next_pred_id,
    !PredTable ^ next_pred_id := PredId + 1.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
