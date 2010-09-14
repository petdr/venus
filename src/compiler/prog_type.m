%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module prog_type.
:- interface.

:- import_module prog_data.

:- import_module list.

%------------------------------------------------------------------------------%

:- func type_list_vars(list(prog_type)) = list(tvar).
:- func type_vars(prog_type) = list(tvar).

%------------------------------------------------------------------------------%

:- func apply_variable_renaming_to_type_list(tvar_renaming, list(prog_type)) = list(prog_type).
:- func apply_variable_renaming_to_type(tvar_renaming, prog_type) = prog_type.
:- func apply_variable_renaming_to_tvar(tvar_renaming, tvar) = tvar.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module map.

type_list_vars(Types) =
    list.sort_and_remove_dups(list.condense(list.map(type_vars, Types))).
    
type_vars(atomic_type(_)) = [].
type_vars(type_variable(TVar)) = [TVar].
type_vars(higher_order_type(Args)) = type_list_vars(Args).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

apply_variable_renaming_to_type_list(Renaming, Types) =
    list.map(apply_variable_renaming_to_type(Renaming), Types).
    
apply_variable_renaming_to_type(_Renaming, Type @ atomic_type(_)) = Type.
apply_variable_renaming_to_type(Renaming, type_variable(TVar)) =
    type_variable(apply_variable_renaming_to_tvar(Renaming, TVar)).
apply_variable_renaming_to_type(Renaming, higher_order_type(Args)) =
    higher_order_type(apply_variable_renaming_to_type_list(Renaming, Args)).

apply_variable_renaming_to_tvar(Renaming, TVar0) =
    ( map.search(Renaming, TVar0, TVar) ->
        TVar
    ;
        TVar0
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
