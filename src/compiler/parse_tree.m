%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
%
% Module: parse_tree
% Author: peter@emailross.com
%
% Convert a file into a parse tree representation.
%
%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module parse_tree.

:- interface.

:- import_module error_util.
:- import_module prog_item.

:- import_module io.
:- import_module list.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_items(string::in, list(item)::out, list(error_spec)::out, io::di, io::uo) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module prog_data.

:- import_module pair.
:- import_module parser.
:- import_module require.
:- import_module term.
:- import_module term_io.
:- import_module varset.

parse_items(FileName, Items, Errors, !IO) :-
    parser.read_term(ReadTermResult, !IO),
    ( ReadTermResult = term(Varset, Term),
        parse_item(Varset, Term, ParseResult),
        ( ParseResult = ok(Item),
            parse_items(FileName, Items0, Errors, !IO),
            Items = [Item | Items0]

        ; ParseResult = error(Errors),
            Items = []
        )

    ; ReadTermResult = eof,
        Items = [],
        Errors = []

    ; ReadTermResult = error(Error, Line),
        Items = [],
        Errors = [simple_error_msg(context(FileName, Line), Error)]
    ).

:- type parse_result(T)
    --->    ok(T)
    ;       error(list(error_spec))
    .
    
:- pred parse_item(varset::in, term::in, parse_result(item)::out) is det.

parse_item(Varset, Term, Result) :-
    ( Term = term.functor(term.atom(":-"), [DeclTerm], Context) ->
        parse_decl(Varset, DeclTerm, Context, Result)

    ; Term = term.functor(term.atom(":-"), [HeadTerm, BodyTerm], Context) ->
        parse_clause(Varset, HeadTerm, BodyTerm, Context, ClauseResult),
        ( ClauseResult = ok(Clause),
            Result = ok(clause(Clause))
        ; ClauseResult = error(Errors),
            Result = error(Errors)
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Unable to parse the term")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_decl(varset::in, term::in, context::in, parse_result(item)::out) is det.

parse_decl(Varset, Term, _Context, Result) :-
    parse_attrs_and_decl(Varset, Term, [], Result).

%------------------------------------------------------------------------------%

:- type decl_attribute
    --->    decl_attribute_constraints(quant_type, term)
    .

:- type quant_type
    --->    quant_type_univ
    .

:- pred parse_attrs_and_decl(varset::in, term::in, list(decl_attribute)::in, parse_result(item)::out) is det.

parse_attrs_and_decl(Varset, Term, !.Attributes, Result) :-
    ( Term = term.functor(term.atom(Functor), Args, Context) ->
        (
            parse_decl_attribute(Functor, Args, Attribute, SubTerm)
        ->
            !:Attributes = [Attribute | !.Attributes],
            parse_attrs_and_decl(Varset, SubTerm, !.Attributes, Result)
        ;
            parse_attributed_decl(Varset, Functor, Args, !.Attributes, Context, Result0)
        ->
            Result = Result0
        ;
            Result = error([simple_error_msg(get_term_context(Term), "unrecognized declaration")])
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "atom expected after :-")])
    ).

%------------------------------------------------------------------------------%

:- pred parse_decl_attribute(string::in, list(term)::in, decl_attribute::out, term::out) is semidet.

parse_decl_attribute(Functor, ArgTerms, Attribute, SubTerm) :-
    (
        Functor = "<=",
        ArgTerms = [SubTerm, ConstraintsTerm],
        Attribute = decl_attribute_constraints(quant_type_univ, ConstraintsTerm)
    ).

%------------------------------------------------------------------------------%

    % The decl_attribute are in the order outermost to innermost.
:- pred parse_attributed_decl(varset::in,
    string::in, list(term)::in, list(decl_attribute)::in, context::in, parse_result(item)::out) is semidet.

parse_attributed_decl(Varset, Functor, ArgTerms, Attrs, Context, Result) :-
    (
        Functor = "pred",
        ArgTerms = [PredTerm],
        parse_pred_decl(Varset, PredTerm, Context, Result)
    ;
        Functor = "type",
        ArgTerms = [TypeTerm],
        parse_type_defn(Varset, TypeTerm, Context, Result0),
        check_no_attributes(Attrs, Context, Result0, Result)
    ;
        Functor = "typeclass",
        ArgTerms = [TypeclassTerm],
        parse_typeclass(Varset, TypeclassTerm, Context, Result0),
        check_no_attributes(Attrs, Context, Result0, Result)
    ).

:- pred check_no_attributes(list(decl_attribute)::in, context::in, parse_result(T)::in, parse_result(T)::out) is det.

check_no_attributes([], _Context, !Result).
check_no_attributes([_|_], Context, _, Result) :-
        % XXX improve this error message
    Result = error([simple_error_msg(Context, "Decl shouldn't have attributes")]).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_pred_decl(varset::in, term::in, context::in, parse_result(item)::out) is det.

parse_pred_decl(Varset, PredTerm, Context, Result) :-
    ( parse_sym_name(PredTerm, SymName, PredArgs) ->
        parse_type_list(PredArgs, ResultPredArgs),
        ( ResultPredArgs = ok(Types),
            Result = ok(pred_decl(pred_decl(SymName, Types, coerce(Varset), Context)))
        ; ResultPredArgs = error(Errors),
            Result = error(Errors)
        )
    ;
        Result = error([simple_error_msg(Context, "Unable to parse predicate declaration")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_type_defn(varset::in, term::in, context::in, parse_result(item)::out) is det.

parse_type_defn(Varset, TypeTerm, Context, Result) :-
    ( TypeTerm = functor(atom("--->"), [TypeNameTerm, TypeBodyTerm], _) ->
        parse_type_head(TypeNameTerm, TypeNameResult),
        parse_type_body(TypeBodyTerm, TypeBodyResult),
        Combine = (func({TypeName, TypeVars}, TypeBody) =
            type_defn(type_defn(TypeName, TypeVars, coerce(Varset), TypeBody, Context))),
        Result = combine_results(Combine, TypeNameResult, TypeBodyResult)
    ;
        Result = error([simple_error_msg(Context, "Unable to parse type definition")])
    ).

%------------------------------------------------------------------------------%

:- pred parse_type_head(term::in, parse_result({sym_name, list(prog_type)})::out) is det.

parse_type_head(Term @ functor(_Const, _Args, Context), Result) :-
    ( parse_sym_name(Term, SymName, Args) ->
        ( var_list(Args, TypeVars) ->
            Result = ok({SymName, list.map(func(V) = type_variable(V), TypeVars)})
        ;
            Result = error([simple_error_msg(Context, "Expected a list of type variables")])
        )
    ;
        Result = error([simple_error_msg(Context, "Expected a name")])
    ).
parse_type_head(variable(_Var, Context), Result) :-
    Result = error([simple_error_msg(Context, "Unexpected variable")]).
    
%------------------------------------------------------------------------------%

:- pred parse_type_body(term::in, parse_result(item_type_body)::out) is det.

parse_type_body(Term, Result) :-
    parse_data_constructor_list(Term, ConsListResult),
    ( ConsListResult = ok(List),
        Result = ok(discriminated_union(List))
    ; ConsListResult = error(Errs),
        Result = error(Errs)
    ).

:- pred parse_data_constructor_list(term::in, parse_result(list(item_data_constructor))::out) is det.

parse_data_constructor_list(Term, Result) :-
    ( Term = functor(atom(";"), [TermA, TermB], _Context) ->
        parse_data_constructor_list(TermA, ResultA),
        parse_data_constructor_list(TermB, ResultB),
        Result = combine_results(list.append, ResultA, ResultB)
    ;
        parse_data_constructor(Term, DataConsResult),
        ( DataConsResult = ok(DataConstructor),
            Result = ok([DataConstructor])
        ; DataConsResult = error(Errs),
            Result = error(Errs)
        )
    ).

:- pred parse_data_constructor(term::in, parse_result(item_data_constructor)::out) is det.

parse_data_constructor(Term, Result) :-
    ( parse_sym_name(Term, SymName, TermArgs) ->
        parse_type_list(TermArgs, TypeListResult),
        ( TypeListResult = ok(Types),
            Result = ok(data_constructor(SymName, Types, get_term_context(Term)))
        ; TypeListResult = error(Errs),
            Result = error(Errs)
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Expected a data constructor")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_typeclass(varset::in, term::in, term.context::in, parse_result(item)::out) is det.

parse_typeclass(Varset, Term, TypeclassContext, Result) :-
    ( Term = term.functor(atom("where"), [NameTerm, ListTerm], _Context) ->
        ( parse_sym_name(NameTerm, SymName, TermArgs) ->
            (
                var_list(TermArgs, TypeVars),
                TermArgs = [_|_]
            ->
                TVarset = coerce(Varset),
                parse_list(parse_typeclass_method(TVarset), ListTerm, MethodsResult),
                ( MethodsResult = ok(Methods),
                    TypeParams = list.map(func(V) = type_variable(V), TypeVars),
                    TypeClassDefn = typeclass_defn(SymName, TypeParams, TVarset, Methods, TypeclassContext),
                    Result = ok(typeclass_defn(TypeClassDefn))
                ; MethodsResult = error(Errs),
                    Result = error(Errs)
                )
            ;
                Msg = "Expected a list of type variables in the typeclass name",
                Result = error([simple_error_msg(get_term_context(NameTerm), Msg)])
            )
        ;
            Result = error([simple_error_msg(get_term_context(Term), "Unable to parse the typeclass name")])
        )
    ;
        Result = error([simple_error_msg(TypeclassContext, "Unable to parse the typeclass")])
    ).

:- pred parse_typeclass_method(tvarset::in, term::in, parse_result(class_method)::out) is det.

parse_typeclass_method(TVarset, Term, Result) :-
    ( Term = functor(atom("pred"), [PredTerm], Context) ->
        ( parse_sym_name(PredTerm, SymName, PredArgs) ->
            parse_type_list(PredArgs, ResultPredArgs),
            ( ResultPredArgs = ok(Types),
                Result = ok(class_method(SymName, Types, TVarset, Context))
            ; ResultPredArgs = error(Errors),
                Result = error(Errors)
            )
        ;
            Result = error([simple_error_msg(get_term_context(PredTerm), "typeclass method name")])
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Expected pred method")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_clause(varset::in, term::in, term::in, term.context::in, parse_result(item_clause)::out) is det.

parse_clause(Varset, HeadTerm, BodyTerm, ClauseContext, Result) :-
    parse_clause_head(Varset, HeadTerm, HeadResult),
    parse_clause_body(BodyTerm, BodyResult),
    Combine = (func({Name, Args}, BodyGoal) = clause(sym_name([], Name), Args, BodyGoal, coerce(Varset), ClauseContext)),
    Result = combine_results(Combine, HeadResult, BodyResult).

%------------------------------------------------------------------------------%

:- pred parse_clause_head(varset::in, term::in, parse_result({string, list(prog_term)})::out) is det.

parse_clause_head(_Varset, HeadTerm, Result) :-
    (
        HeadTerm = term.functor(term.atom(Name), HeadArgs, _HeadContext)
    ->
        Result = ok({Name, list.map(coerce, HeadArgs)})
    ;
        Result = error([simple_error_msg(get_term_context(HeadTerm), "Unable to parse clause head")])
    ).

%------------------------------------------------------------------------------%

:- pred parse_clause_body(term::in, parse_result(goal)::out) is det.

parse_clause_body(Term @ functor(Const, Args, Context), Result) :-
    ( Const = atom(Atom) ->
            % Parse a conjunction
        ( Atom = ",", Args = [TermA, TermB] ->
            parse_clause_body(TermA, ResultA),
            parse_clause_body(TermB, ResultB),
            Result = combine_results(func(GoalA, GoalB) = conj(GoalA, GoalB) - Context, ResultA, ResultB)

            % Parse a disjunction
        ; Atom = ";", Args = [TermA, TermB] ->
            parse_clause_body(TermA, ResultA),
            parse_clause_body(TermB, ResultB),
            Result = combine_results(func(GoalA, GoalB) = disj(GoalA, GoalB) - Context, ResultA, ResultB)

            % Parse a unification or object call
        ; Atom = "=", Args = [TermA, TermB] ->
            ( parse_object_method(TermB, Method) ->
                Result = ok(object_function_call(coerce(TermA), Method) - Context)
            ;
                Result = ok(unify(coerce(TermA), coerce(TermB)) - Context)
            )
        ; parse_object_method(Term, Method) ->
            Result = ok(object_void_call(Method) - Context)
        ; parse_sym_name(Term, SymName, SymNameArgs) ->
            Result = ok(call(SymName, list.map(coerce, SymNameArgs)) - Context)
        ;
            Result = ok(call(sym_name([], Atom), list.map(coerce, Args)) - Context)
        )
    ;
        Result = error([simple_error_msg(Context, "Unable to parse the clause body")])
    ).
parse_clause_body(variable(_Var, Context), Result) :-
    Result = error([simple_error_msg(Context, "Unexpected variable")]).

%------------------------------------------------------------------------------%

:- pred parse_object_method(term::in, object_method::out) is semidet.

parse_object_method(functor(atom("."), Args, _Context), Method) :-
    Args = [variable(ObjectVar, _VarContext), functor(atom(MethodName), MethodArgs, _MethodContext)],
    Method = object_method(coerce_var(ObjectVar), sym_name([], MethodName), list.map(coerce, MethodArgs)).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_constraint_list(term::in, parse_result(list(prog_constraint))::out) is det.

parse_constraint_list(Term, Result) :-
    ( Term = functor(atom(","), [TermA, TermB], _) ->
        parse_constraint_list(TermA, ResultA),
        parse_constraint_list(TermB, ResultB),
        Result = combine_results(list.append, ResultA, ResultB)
    ;
        parse_constraint(Term, ConstraintResult),
        ( ConstraintResult = ok(Constraint),
            Result = ok([Constraint])
        ; ConstraintResult = error(Errs),
            Result = error(Errs)
        )
    ).

:- pred parse_constraint(term::in, parse_result(prog_constraint)::out) is det.

parse_constraint(Term, Result) :-
    ( parse_sym_name(Term, SymName, Args) ->
        ( var_list(Args, TypeVars) ->
            Result = ok(prog_constraint(SymName, list.map(func(V) = type_variable(V), TypeVars)))
        ;
            Result = error([simple_error_msg(get_term_context(Term), "Expected a list of type variables")])
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Expected a name")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_sym_name(term::in, sym_name::out, list(term)::out) is semidet.

parse_sym_name(Term, sym_name(Qualifiers, Name), Args) :-
    parse_qualified_name(Term, Qualifiers, Name, Args).

:- pred parse_qualified_name(term::in, list(string)::out, string::out, list(term)::out) is semidet.

parse_qualified_name(functor(atom(Atom), Args, _Context), Qualifiers, Name, NameArgs) :-
    ( Atom = "." ->
        Args = [functor(ConstA, ArgsA, _), functor(atom(Name), NameArgs, _)],
        parse_qualifiers(ConstA, ArgsA, Qualifiers)
    ;
        Qualifiers = [],
        Name = Atom,
        NameArgs = Args
    ).

:- pred parse_qualifiers(const::in, list(term)::in, list(string)::out) is semidet.

parse_qualifiers(atom(Atom), Args, Qualifiers) :-
    ( Atom = "." ->
        Args = [functor(SubConst, SubArgs, _), functor(atom(Name), [], _)],
        parse_qualifiers(SubConst, SubArgs, Qualifiers0),
        Qualifiers = Qualifiers0 ++ [Name]
    ;
        Args = [],
        Qualifiers = [Atom]
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_type(term::in, parse_result(prog_type)::out) is det.

parse_type(variable(Var, _), ok(type_variable(coerce_var(Var)))).
parse_type(Term @ functor(_, _, _), Result) :-
    ( parse_qualified_name(Term, Qualifiers, TypeCtor, TypeCtorArgs) ->
        ( Qualifiers = [], TypeCtor = "int", TypeCtorArgs = [] ->
            Result = ok(atomic_type(atomic_type_int))
        ; Qualifiers = [], TypeCtor = "float", TypeCtorArgs = [] ->
            Result = ok(atomic_type(atomic_type_float))
        ; Qualifiers = [], TypeCtor = "pred" ->
            parse_type_list(TypeCtorArgs, ResultTypeList),
            ( ResultTypeList = ok(Types),
                Result = ok(higher_order_type(Types))
            ; ResultTypeList = error(Errors),
                Result = error(Errors)
            )
        ;
            parse_type_list(TypeCtorArgs, ResultTypeList),
            ( ResultTypeList = ok(Types),
                Result = ok(defined_type(sym_name(Qualifiers, TypeCtor), Types))
            ; ResultTypeList = error(Errors),
                Result = error(Errors)
            )
        )
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Expected a name")])
    ).

%------------------------------------------------------------------------------%

:- pred parse_type_list(list(term)::in, parse_result(list(prog_type))::out) is det.

parse_type_list([], ok([])).
parse_type_list([Term | Terms], Result) :-
    parse_type(Term, ResultTerm),
    parse_type_list(Terms, ResultTerms),
    Result = combine_results(list.cons, ResultTerm, ResultTerms).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred parse_list(pred(term, parse_result(T))::in(pred(in, out) is det), term::in, parse_result(list(T))::out) is det.

parse_list(ParseListItem, Term, Result) :-
    ( Term = term.functor(atom("[]"), [], _) ->
        Result = ok([])
    ; Term = term.functor(atom("[|]"), [HeadTerm, TailTerm], _) ->
        ParseListItem(HeadTerm, ItemResult),
        parse_list(ParseListItem, TailTerm, Result0),
        Result = combine_results(list.cons, ItemResult, Result0)
    ;
        Result = error([simple_error_msg(get_term_context(Term), "Expected a list")])
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- pred var_list(list(term)::in, list(var(T))::out) is semidet.

var_list([], []).
var_list([Term | Terms], [Var | Vars]) :-
    Term = variable(GenericVar, _),
    coerce_var(GenericVar, Var),
    var_list(Terms, Vars).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func simple_error_msg(term.context, string) = error_spec.

simple_error_msg(Context, Msg) = error_spec(severity_error, [simple_msg(Context, [always([words(Msg)])])]).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func combine_results(func(T, U) = V, parse_result(T), parse_result(U)) = parse_result(V).

combine_results(Combine, ok(A), ok(B)) = ok(Combine(A, B)).
combine_results(_Combine, error(A), ok(_B)) = error(A).
combine_results(_Combine, ok(_A), error(B)) = error(B).
combine_results(_Combine, error(A), error(B)) = error(A ++ B).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
