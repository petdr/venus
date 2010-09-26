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
    ;       instance_defn(item_instance_defn)
    ;       pred_decl(item_pred_decl)
    ;       type_defn(item_type_defn)
    ;       typeclass_defn(item_typeclass_defn)
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

:- type item_instance_defn
    --->    instance_defn(
                instance_name           :: sym_name,
                instance_args           :: list(prog_type),
                instance_constraints    :: list(prog_constraint),
                instance_tvarset        :: tvarset
            ).

:- type item_pred_decl
    --->    pred_decl(
                pred_decl_name              :: sym_name,
                pred_decl_types             :: list(prog_type),
                pred_decl_tvarset           :: tvarset,
                pred_decl_univ_constraints  :: list(prog_constraint),
                pred_decl_context           :: term.context
            ).

:- type item_type_defn
    --->    type_defn(
                type_defn_name      :: sym_name,
                type_defn_params    :: list(type_param),
                type_defn_tvarset   :: tvarset,
                type_defn_body      :: item_type_body,
                type_defn_context   :: term.context
            ).

:- type item_type_body
    --->    discriminated_union(
                list(item_data_constructor)
            ).

:- type item_data_constructor
    --->    data_constructor(
                data_cons_name      :: sym_name,
                data_cons_args      :: list(prog_type),
                data_cons_context   :: term.context
            ).

:- type item_typeclass_defn
    --->    typeclass_defn(
                typeclass_name      :: sym_name,
                typeclass_args      :: list(type_param),
                typeclass_tvarset   :: tvarset,
                typeclass_methods   :: list(class_method),
                typeclass_context   :: term.context
            ).

:- type class_method
    --->    class_method(
                method_name         :: sym_name,
                method_args         :: list(prog_type),
                method_tvarset      :: tvarset,
                method_context      :: term.context
            ).

:- type goal == pair(goal_expr, term.context).
                
:- type goal_expr
    --->    conj(goal, goal)
    ;       disj(goal, goal)
    ;       unify(prog_term, prog_term)
    ;       true_expr
    ;       fail_expr
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
