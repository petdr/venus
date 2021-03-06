%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% 
% Module: prog_data
% Author: peter@emailross.com
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module prog_data.

:- interface.

:- import_module index.
:- import_module list.
:- import_module map.
:- import_module term.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type prog ---> prog.

:- type prog_context == term.context.
:- type prog_term == term(prog).
:- type prog_var == var(prog).
:- type prog_varset == varset(prog).

%------------------------------------------------------------------------------%

:- type module_name == list(string).

:- type sym_name
    --->    sym_name(
                module_qualifiers   :: module_name,
                local_name          :: string
            ).

:- type arity == int.

:- type sym_name_and_arity
    --->    sym_name / arity.

:- type type_ctor
    --->    type_ctor(sym_name, arity).

:- instance index_key(sym_name).

%------------------------------------------------------------------------------%

:- type tvar_type ---> tvar_type.

:- type tvar ==  var(tvar_type).
:- type tvarset ==  varset(tvar_type).
:- type tvar_renaming == map(tvar, tvar).

:- type prog_type
    --->    atomic_type(atomic_type)
    ;       type_variable(tvar)
    ;       higher_order_type(list(prog_type))
    ;       defined_type(sym_name, list(prog_type))
    .

:- type atomic_type
    --->    atomic_type_int
    ;       atomic_type_float
    .

    % A type_param is a prog_type which is a type_variable.
:- type type_param == prog_type.

    % Similar to varset.merge_subst but produces a tvar_renaming
    % instead of a substitution, which is more suitable for types.
    %
:- pred tvarset_merge_renaming(tvarset::in, tvarset::in, tvarset::out,
    tvar_renaming::out) is det.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type prog_constraint
    --->    prog_constraint(
                constraint_name     :: sym_name,
                constraint_params   :: list(type_param)
            ).

:- type prog_object
    --->    prog_object(
                object_name         :: sym_name,
                object_params       :: list(type_param)
            ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- instance index_key(sym_name) where [
    (smaller_key(sym_name([_Q | Qs], Name), sym_name(Qs, Name)))
].

%------------------------------------------------------------------------------%

:- import_module compiler_util.

tvarset_merge_renaming(TVarSetA, TVarSetB, TVarSet, Renaming) :-
    varset.merge_subst(TVarSetA, TVarSetB, TVarSet, Subst),
    map.map_values_only(convert_subst_term_to_tvar, Subst, Renaming).

:- pred convert_subst_term_to_tvar(term(tvar_type)::in, tvar::out) is det.

convert_subst_term_to_tvar(variable(TVar, _), TVar).
convert_subst_term_to_tvar(functor(_, _, _), _) :-
    unexpected(this_file, "non-variable found in renaming").

:- func this_file = string.
this_file = "prog_data.m".

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
