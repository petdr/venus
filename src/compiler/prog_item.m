%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
:- module prog_item.

:- interface.

:- import_module prog_data.

:- import_module list.
:- import_module pair.
:- import_module term.

:- type item
    --->    clause(item_clause)
    ;       declaration(item_declaration)
    .

:- type item_clause
    --->    clause(
                clause_name         :: sym_name,
                clause_args         :: list(prog_term),
                clause_goal         :: goal,
                clause_varset       :: prog_varset,
                clause_context      :: term.context
            )
    .

:- type item_declaration
    --->    pred_decl(
                pred_decl_name      :: sym_name,
                pred_decl_types     :: list(prog_type),
                pred_decl_tvarset   :: tvarset,
                pred_decl_context   :: term.context
            )
    .

:- type goal == pair(goal_expr, term.context).
                
:- type goal_expr
    --->    conj(goal, goal)
    ;       unify(prog_term, prog_term)
    ;       call(sym_name, list(prog_term))
    ;       object_void_call(object_method)
    ;       object_function_call(prog_term, object_method)
    .

:- type object_method
    --->    object_method(
                object_var      :: prog_var,
                object_method   :: sym_name,
                object_args     :: list(prog_term)
            ).
        
:- implementation.
