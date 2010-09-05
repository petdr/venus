:- module prog_data.

:- interface.

:- import_module term.
:- import_module varset.

:- type prog_type ---> prog_type.

:- type prog_term == term(prog_type).
:- type prog_var == var(prog_type).
:- type prog_varset == varset(prog_type).

:- type sym_name == string.
