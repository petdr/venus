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
    ;
        Result = error([error("Unknown term", 0)])
    ).

:- pred parse_clause(varset::in, term::in, term::in, parse_result(item_clause)::out, io::di, io::uo) is det.

parse_clause(Varset, HeadTerm, BodyTerm, Result, !IO) :-
    parse_clause_head(Varset, HeadTerm, HeadResult, !IO),
    ( HeadResult = ok({Name, Args}),
        parse_clause_body(BodyTerm, BodyResult, !IO),
        ( BodyResult = ok(BodyGoal),
            Result = ok(clause(Name, Args, BodyGoal, coerce(Varset)))
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
        ;
            Result = ok(call(Atom, list.map(coerce, Args)))
        )
    ;
        Result = error([error("expected an atom for the goal", 0)])
    ).
parse_clause_body(variable(_Var, _Context), Result, !IO) :-
    Result = error([error("unexpected variable", 0)]).


:- pred parse_object_method(term::in, object_method::out) is semidet.

parse_object_method(functor(atom("."), Args, _Context), Method) :-
    Args = [variable(ObjectVar, _VarContext), functor(atom(MethodName), MethodArgs, _MethodContext)],
    Method = object_method(coerce_var(ObjectVar), MethodName, list.map(coerce, MethodArgs)).
