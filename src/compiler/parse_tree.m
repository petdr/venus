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

:- import_module prog_item.

:- import_module io.
:- import_module list.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type parse_error
    --->    error(string, int).

:- pred parse_items(list(item)::out, list(parse_error)::out, io::di, io::uo) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module prog_data.

:- import_module parser.
:- import_module require.
:- import_module term.
:- import_module term_io.
:- import_module varset.

parse_items(Items, Errors, !IO) :-
    parser.read_term(ReadTermResult, !IO),
    ( ReadTermResult = term(Varset, Term),
        parse_item(Varset, Term, ParseResult, !IO),
        ( ParseResult = ok(Item),
            parse_items(Items0, Errors, !IO),
            Items = [Item | Items0]

        ; ParseResult = error(Errors),
            Items = []
        )

    ; ReadTermResult = eof,
        Items = [],
        Errors = []

    ; ReadTermResult = error(ErrStr, ErrInt),
        Items = [],
        Errors = [error(ErrStr, ErrInt)]
    ).

:- type parse_result(T)
    --->    ok(T)
    ;       error(list(parse_error))
    .
    
:- pred parse_item(varset::in, term::in, parse_result(item)::out, io::di, io::uo) is det.

parse_item(Varset, Term, Result, !IO) :-
    ( Term = term.functor(term.atom(":-"), [HeadTerm, BodyTerm], _Context) ->
        parse_clause(Varset, HeadTerm, BodyTerm, ClauseResult, !IO),
        ( ClauseResult = ok(Clause),
            Result = ok(clause(Clause))
        ; ClauseResult = error(Errors),
            Result = error(Errors)
        )
    ; Term = term.functor(term.atom(":-"), [functor(atom("pred"), [PredTerm], _)], _Context) ->
        ( parse_qualified_name(PredTerm, Qualifiers, Name, PredArgs) ->
            parse_type_list(PredArgs, ResultPredArgs, !IO),
            ( ResultPredArgs = ok(Types),
                Result = ok(declaration(pred_decl(sym_name(Qualifiers, Name), Types, coerce(Varset))))
            ; ResultPredArgs = error(Errors),
                Result = error(Errors)
            )
        ;
            Result = error([error("pred error", 0)])
        )
    ;
        Result = error([error("Unknown term", 0)])
    ).

:- pred parse_clause(varset::in, term::in, term::in, parse_result(item_clause)::out, io::di, io::uo) is det.

parse_clause(Varset, HeadTerm, BodyTerm, Result, !IO) :-
    parse_clause_head(Varset, HeadTerm, HeadResult, !IO),
    ( HeadResult = ok({Name, Args}),
        parse_clause_body(BodyTerm, BodyResult, !IO),
        ( BodyResult = ok(BodyGoal),
            Result = ok(clause(sym_name([], Name), Args, BodyGoal, coerce(Varset)))
        ; BodyResult = error(Errors),
            Result = error(Errors)
        )
    ; HeadResult = error(Errors),
        Result = error(Errors)
    ).

:- pred parse_clause_head(varset::in, term::in, parse_result({string, list(prog_term)})::out, io::di, io::uo) is det.

parse_clause_head(_Varset, HeadTerm, Result, !IO) :-
    (
        HeadTerm = term.functor(term.atom(Name), HeadArgs, _HeadContext)
    ->
        Result = ok({Name, list.map(coerce, HeadArgs)})
    ;
        Result = error([error("XXX", 0)])
    ).

:- pred prog_var_list(list(term)::in, list(prog_var)::out) is semidet.

prog_var_list([], []).
prog_var_list([Term | Terms], [ProgVar | ProgVars]) :-
    Term = variable(Var, _),
    coerce_var(Var, ProgVar),
    prog_var_list(Terms, ProgVars).

:- pred parse_clause_body(term::in, parse_result(goal)::out, io::di, io::uo) is det.

parse_clause_body(Term @ functor(Const, Args, _Context), Result, !IO) :-
    ( Const = atom(Atom) ->
            % Parse a conjunction
        ( Atom = ",", Args = [TermA, TermB] ->
            parse_clause_body(TermA, ResultA, !IO),
            ( ResultA = ok(GoalA),
                parse_clause_body(TermB, ResultB, !IO),
                ( ResultB = ok(GoalB),
                    Result = ok(conj(GoalA, GoalB))
                ; ResultB = error(Errors),
                    Result = error(Errors)
                )
            ; ResultA = error(Errors),
                Result = error(Errors)
            )

            % Parse a unification or object call
        ; Atom = "=", Args = [TermA, TermB] ->
            ( parse_object_method(TermB, Method) ->
                Result = ok(object_function_call(coerce(TermA), Method))
            ;
                Result = ok(unify(coerce(TermA), coerce(TermB)))
            )
        ; parse_object_method(Term, Method) ->
            Result = ok(object_void_call(Method))
        ; parse_qualified_name(Term, Qualifiers, Name, SymNameArgs) ->
            Result = ok(call(sym_name(Qualifiers, Name), list.map(coerce, SymNameArgs)))
        ;
            Result = ok(call(sym_name([], Atom), list.map(coerce, Args)))
        )
    ;
        Result = error([error("expected an atom for the goal", 0)])
    ).
parse_clause_body(variable(_Var, _Context), Result, !IO) :-
    Result = error([error("unexpected variable", 0)]).

:- pred parse_object_method(term::in, object_method::out) is semidet.

parse_object_method(functor(atom("."), Args, _Context), Method) :-
    Args = [variable(ObjectVar, _VarContext), functor(atom(MethodName), MethodArgs, _MethodContext)],
    Method = object_method(coerce_var(ObjectVar), sym_name([], MethodName), list.map(coerce, MethodArgs)).

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

:- pred parse_type(term::in, parse_result(prog_type)::out, io::di, io::uo) is det.

parse_type(variable(Var, _), ok(type_variable(coerce_var(Var))), !IO).
parse_type(Term @ functor(_, _, _), Result, !IO) :-
    ( parse_qualified_name(Term, Qualifiers, TypeCtor, TypeCtorArgs) ->
        ( Qualifiers = [], TypeCtor = "int", TypeCtorArgs = [] ->
            Result = ok(atomic_type(atomic_type_int))
        ; Qualifiers = [], TypeCtor = "float", TypeCtorArgs = [] ->
            Result = ok(atomic_type(atomic_type_float))
        ; Qualifiers = [], TypeCtor = "pred" ->
            parse_type_list(TypeCtorArgs, ResultTypeList, !IO),
            ( ResultTypeList = ok(Types),
                Result = ok(higher_order_type(Types))
            ; ResultTypeList = error(Errors),
                Result = error(Errors)
            )
        ;
            Result = error([error("unknown type", 0)])
        )
        
    ;
        Result = error([error("unknown type", 0)])
    ).

:- pred parse_type_list(list(term)::in, parse_result(list(prog_type))::out, io::di, io::uo) is det.

parse_type_list([], ok([]), !IO).
parse_type_list([Term | Terms], Result, !IO) :-
    parse_type(Term, ResultTerm, !IO),
    parse_type_list(Terms, ResultTerms, !IO),
    ( ResultTerm = ok(Type),
        ( ResultTerms = ok(Types),
            Result = ok([Type | Types])
        ; ResultTerms = error(Errors),
            Result = error(Errors)
        )
    ; ResultTerm = error(Errors),
        ( ResultTerms = ok(_),
            Result = error(Errors)
        ; ResultTerms = error(Errors2),
            Result = error(Errors ++ Errors2)
        )
    ).


