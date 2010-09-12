%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: make_hlds
% Author: peter@emailross.com
%
% Convert the parse tree item list into the HLDS representation.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module make_hlds.

:- interface.

:- import_module hlds.
:- import_module prog_data.
:- import_module prog_item.

:- import_module io.
:- import_module list.

    % Given a list of items convert it into the HLDS representation.
    %
:- pred make_hlds(module_name::in, list(item)::in, hlds::out, io::di, io::uo) is det.

:- implementation.

:- import_module hlds_goal.
:- import_module hlds_pred.
:- import_module predicate_table.
:- import_module prog_data.
:- import_module sym_name.

:- import_module maybe.
:- import_module require.
:- import_module svvarset.
:- import_module term.
:- import_module varset.

:- type make_hlds_info
    --->    make_hlds_info(
                mi_module_name  :: module_name
            ).

make_hlds(ModuleName, Items, !:HLDS, !IO) :-
    Info = make_hlds_info(ModuleName),

    init_hlds(!:HLDS),

        % Process each of the declarations
    list.foldl(process_decls(Info), Items, !HLDS),

        % Insert each clause into the HLDS.
    list.foldl(process_clause_items(Info), Items, !HLDS).


:- pred process_decls(make_hlds_info::in, item::in, hlds::in, hlds::out) is det.

process_decls(_Info, clause(_), !HLDS).
process_decls(Info, declaration(Decl), !HLDS) :-
    Decl = pred_decl(PredName, PredTypes, _PredTVarset),
    Arity = list.length(PredTypes),

    ( partially_qualified_sym_name_matches_module_name(Info ^ mi_module_name, PredName) ->
        ImportStatus = is_local
    ;
        ImportStatus = is_imported
    ),

    Pred = hlds_pred(invalid_pred_id, PredName, Arity, ImportStatus, [], varset.init, no_goal),

    set_hlds_pred(Pred, _PredId, !.HLDS ^ predicate_table, PredTable),
    !HLDS ^ predicate_table := PredTable.


    % The pass which processes each of the clauses.
    %
:- pred process_clause_items(make_hlds_info::in, item::in, hlds::in, hlds::out) is det.

process_clause_items(_Info, declaration(_), !HLDS).
process_clause_items(Info, clause(Clause), !HLDS) :-
    add_clause(Info, Clause, !HLDS).

:- pred add_clause(make_hlds_info::in, item_clause::in, hlds::in, hlds::out) is det.

add_clause(Info, clause(Name, Args, Goal, !.Varset), !HLDS) :-
    FullName = fully_qualify_name(Info ^ mi_module_name, Name),

        % Convert each arg into a variable and set of unifications
    list.map2_foldl(term_to_shf, Args, HeadVars, HeadGoalsList, !Varset),
        
        % Convert the goal into a HLDS Goal
    goal_to_hlds_goal(Goal, HldsGoal0, !Varset),

        % Now mix the goals up
    HeadGoals = list.condense(HeadGoalsList),
    ( HeadGoals = [] ->
        HldsGoal = HldsGoal0
    ;
        ( HldsGoal0 = conj(ConjGoals) ->
            HldsGoal = conj(HeadGoals ++ ConjGoals)
        ;
            HldsGoal = conj(HeadGoals ++ [HldsGoal0])
        )
    ),

    Arity = list.length(Args),

    ( search_name_arity(!.HLDS ^ predicate_table, FullName, Arity, Pred0) ->
        Goal0 = Pred0 ^ pred_goal,
        ( Goal0 = no_goal,
            Pred = ((Pred0
                ^ pred_args := HeadVars)
                ^ pred_varset := !.Varset)
                ^ pred_goal := goal(HldsGoal)
        ; Goal0 = goal(_),
            error("XXX: don't handle multiple clauses yet.")
        )
    ;
        Pred = hlds_pred(invalid_pred_id, FullName, Arity, is_local, HeadVars, !.Varset, goal(HldsGoal))
    ),
    
    set_hlds_pred(Pred, _PredId, !.HLDS ^ predicate_table, PredTable),
    !HLDS ^ predicate_table := PredTable.

%------------------------------------------------------------------------------%

:- pred goal_to_hlds_goal(goal::in, hlds_goal::out, prog_varset::in, prog_varset::out) is det.

goal_to_hlds_goal(conj(A, B), Goal, !Varset) :-
    goal_to_hlds_goal(A, GoalA, !Varset),
    goal_to_hlds_goal(B, GoalB, !Varset),
    ( GoalA = conj(ConjGoalsA) ->
        ( GoalB = conj(ConjGoalsB) ->
            Goal = conj(ConjGoalsA ++ ConjGoalsB)
        ;
            Goal = conj(ConjGoalsA ++ [GoalB])
        )
    ;
        ( GoalB = conj(ConjGoalsB) ->
            Goal = conj([GoalA | ConjGoalsB])
        ;
            Goal = conj([GoalA, GoalB])
        )
    ).
goal_to_hlds_goal(unify(TermA, TermB), Goal, !Varset) :-
    ( TermA = variable(VarA, _),
        ( TermB = variable(VarB, _),
            Goal = unify(VarA, rhs_var(VarB))
        ; TermB = functor(FunctorB, ArgsB, _),
            unravel_functor(VarA, FunctorB, ArgsB, GoalsListB, !Varset),
            Goal = conj(GoalsListB)
        )
    ; TermA = functor(FunctorA, ArgsA, _),
        ( TermB = variable(VarB, _),
            unravel_functor(VarB, FunctorA, ArgsA, GoalsListA, !Varset),
            Goal = conj(GoalsListA)
        ; TermB = functor(FunctorB, ArgsB, _),
            new_var(TmpVar, !Varset),
            unravel_functor(TmpVar, FunctorA, ArgsA, GoalsListA, !Varset),
            unravel_functor(TmpVar, FunctorB, ArgsB, GoalsListB, !Varset),
            Goal = conj(GoalsListA ++ GoalsListB)
        )
    ).
goal_to_hlds_goal(call(Name, Args), Goal, !Varset) :-
    list.map2_foldl(term_to_shf, Args, ArgVars, GoalsList, !Varset),
    Goal = conj([call(Name, ArgVars) | list.condense(GoalsList)]).
goal_to_hlds_goal(object_void_call(Method), Goal, !Varset) :-
    method_to_goal(no, Method, Goal, !Varset).
goal_to_hlds_goal(object_function_call(RetArg, Method), Goal, !Varset) :-
    term_to_shf(RetArg, RetVar, RetGoals, !Varset),
    method_to_goal(yes({RetVar, RetGoals}), Method, Goal, !Varset).
    
:- pred method_to_goal(maybe({prog_var, list(hlds_goal)})::in, object_method::in, hlds_goal::out,
    prog_varset::in, prog_varset::out) is det.

method_to_goal(MaybeFunctionCall, object_method(ObjectVar, MethodName, Args), Goal, !Varset) :-
    list.map2_foldl(term_to_shf, Args, ArgVars, BeforeGoalsList, !Varset),
    BeforeGoals = list.condense(BeforeGoalsList),
    ( MaybeFunctionCall = yes({RetVar, RetGoals}),
        MaybeRet = yes(RetVar),
        AfterGoals = RetGoals
    ; MaybeFunctionCall = no,
        MaybeRet = no,
        AfterGoals = []
    ),
    MethodGoal = method_call(ObjectVar, MethodName, ArgVars, MaybeRet),
    ( BeforeGoals = [], AfterGoals = [] ->
        Goal = MethodGoal
    ;
        Goal = conj(BeforeGoals ++ [MethodGoal] ++ AfterGoals)
    ).

%------------------------------------------------------------------------------%

:- pred term_to_shf(prog_term::in, prog_var::out, list(hlds_goal)::out, prog_varset::in, prog_varset::out) is det.

term_to_shf(variable(Var, _Context), Var, [], !Varset).
term_to_shf(functor(Const, Args, _Context), Var, Goals, !Varset) :-
    new_var(Var, !Varset),
    unravel_functor(Var, Const, Args, Goals, !Varset).

:- pred unravel_functor(prog_var::in, const::in, list(prog_term)::in, list(hlds_goal)::out,
    prog_varset::in, prog_varset::out).

unravel_functor(Var, Const0, Args0, Goals, !Varset) :-
    get_qualifiers(Const0, Args0, Qualifiers, Const, Args),
    list.map2_foldl(term_to_shf, Args, ArgVars, GoalsList, !Varset),
    Rhs = rhs_functor(const_to_cons_id(Qualifiers, Const), ArgVars),
    Goals = [unify(Var, Rhs) | list.condense(GoalsList)].
    
:- pred get_qualifiers(const::in, list(prog_term)::in, list(string)::out, const::out, list(prog_term)::out) is det.

get_qualifiers(Const0, Args0, Qualifiers, Const, Args) :-
    ( Const0 = atom("."), Args0 = [functor(SubConst, SubArgs, _), functor(Const1, Args1, _)] ->
        get_qualifiers_2(SubConst, SubArgs, Qualifiers),
        Const = Const1,
        Args = Args1
    ;
        Qualifiers = [],
        Const = Const0,
        Args = Args0
    ).

:- pred get_qualifiers_2(const::in, list(prog_term)::in, list(string)::out) is det.

get_qualifiers_2(Const, Args, Qualifiers) :-
    ( Const = atom("."), Args = [functor(Const1, Args1, _), functor(atom(Name), [], _)] ->
        get_qualifiers_2(Const1, Args1, Qualifiers0),
        Qualifiers = Qualifiers0 ++ [Name]
    ; Const = atom(Name), Args = [] ->
        Qualifiers = [Name]
    ;
        error("get_qualifiers: parsing should pick this error up")
    ).


:- func const_to_cons_id(list(string), const) = cons_id.

const_to_cons_id(Qualifiers, atom(Atom)) = cons(sym_name(Qualifiers, Atom)).
const_to_cons_id(_, integer(Int)) = int_const(Int).
const_to_cons_id(_, string(_)) = func_error("const_to_cons_id: string").
const_to_cons_id(_, float(_)) = func_error("const_to_cons_id: float").
const_to_cons_id(_, implementation_defined(_)) = func_error("const_to_cons_id: implementation_defined").

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
