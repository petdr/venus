%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: hlds_data
% Author: peter@emailross.com
%
% All the hlds types to do with data.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module hlds_data.

:- interface.

:- import_module hlds.
:- import_module hlds_goal.
:- import_module prog_data.

:- import_module index.
:- import_module list.
:- import_module map.
:- import_module term.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type cons_table  ==  index(cons_id, hlds_cons_defn).

    % A cons_defn is the definition of a constructor (i.e. a constant
    % or a functor) for a particular type.
    %
:- type hlds_cons_defn
    --->    hlds_cons_defn(
                cons_type_id        :: cons_id,

                    % The type_ctor which this data constructor belongs to.
                cons_type_ctor      :: type_ctor,

                    % Copies of data from the type_table for this type_ctor
                cons_type_params    :: list(type_param),
                cons_type_tvarset   :: tvarset,

                    % The aguments of this data constructor
                cons_args           :: list(prog_type),

                    % The context of the data constructor
                cons_context        :: prog_context
            ).

:- pred add_hlds_cons_defn_to_cons_table(hlds_cons_defn::in, cons_table::in, cons_table::out) is det.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type type_index == index(sym_name, type_ctor).
:- type type_table == map(type_ctor, hlds_type_defn).

:- type hlds_type_defn
    --->    hlds_type_defn(
                type_ctor           :: type_ctor,
                type_params         :: list(type_param),
                type_tvarset        :: tvarset,
                type_status         :: import_status,
                type_body           :: hlds_type_body,
                type_context        :: term.context
            ).

:- type hlds_type_body
    --->    hlds_du_type(
                list(constructor)
            ).

:- type constructor
    --->    constructor(
                sym_name,
                list(prog_type)
            ).

    % A type_param is a prog_type which is a type_variable.
:- type type_param == prog_type.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

add_hlds_cons_defn_to_cons_table(Defn, !Table) :-
    index.set(Defn ^ cons_type_id, Defn, !Table).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func this_file = string.

this_file = "hlds_data.m".

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
