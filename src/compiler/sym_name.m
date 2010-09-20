%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
:- module sym_name.

:- interface.
:- import_module prog_data.

    %
    % Does the patially qualified sym_name match the given module name?
    %
:- pred partially_qualified_sym_name_matches_module_name(module_name::in, sym_name::in) is semidet.

    %
    % Fully qualify the given sym_name, throws an exception if the
    % sym_name is partially qualified with an incompatible module_name.
    %
:- func fully_qualify_name(module_name, sym_name) = sym_name.

    %
    % Given a file name converts it into the module_name that file represents.
    %
:- func file_name_to_module_name(string) = module_name.

:- implementation.

:- import_module list.
:- import_module require.
:- import_module string.

partially_qualified_sym_name_matches_module_name(ModuleName, SymName) :-
    list.remove_suffix(ModuleName, SymName ^ module_qualifiers, _Prefix).

fully_qualify_name(ModuleName, SymName) = SymName ^ module_qualifiers := ModuleName :-
    ( partially_qualified_sym_name_matches_module_name(ModuleName, SymName) ->
        true
    ;
        error("fully_qualify_name: module qualifiers don't match")
    ).

file_name_to_module_name(FileName0) = ModuleName :-
    ( string.remove_suffix(FileName0, ".m", FileName1) ->
        FileName = FileName1
    ;
        FileName = FileName0
    ),
    ModuleName = string.words_separator(unify('.'), FileName).
