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

:- import_module list.
:- import_module term.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type prog ---> prog.

:- type prog_context == term.context.
:- type prog_term == term(prog).
:- type prog_var == var(prog).
:- type prog_varset == varset(prog).

%------------------------------------------------------------------------------%

:- type sym_name
    --->    sym_name(
                module_qualifiers   :: list(string),
                string
            ).

:- type arity == int.

:- type sym_name_and_arity
    --->    sym_name / arity.


%------------------------------------------------------------------------------%

:- type tvar_type ---> tvar_type.

:- type tvar ==  var(tvar_type).
:- type tvarset ==  varset(tvar_type).

:- type prog_type
    --->    atomic_type(atomic_type)
    ;       type_variable(tvar)
    ;       higher_order_type(list(prog_type))
    .

:- type atomic_type
    --->    atomic_type_int
    .

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
