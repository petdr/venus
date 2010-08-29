:- module parse_tree.

:- interface.

:- import_module io.
:- import_module list.
:- import_module term.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type item
    --->    clause(clause)
    ;       unknown
    .

%------------------------------------------------------------------------------%

:- type clause
    --->    clause(
                clause_name     :: string,
                clause_vars     :: list(prog_var),
                clause_goal     :: hlds_goal,
                clause_varset   :: prog_varset
            ).

%------------------------------------------------------------------------------%

:- type hlds_goal
    --->    unify(
                unify_lhs   :: prog_var,
                unify_rhs   :: unify_rhs
            )
    ;       call(
                call_name   :: string,
                call_args   :: list(prog_var)
            )
    ;       conj(
                conj_goals  :: list(hlds_goal)
            )
    .

:- type unify_rhs
    --->    rhs_var(
                var_var         :: prog_var
            )
    ;       rhs_functor(
                functor_cons_id :: cons_id,
                functor_vars    :: list(prog_var)
            ).

:- type cons_id
    --->    cons(string)
    ;       int_const(int)
    .

%------------------------------------------------------------------------------%

:- type prog_var_type
    --->    prog_var_type.

:- type prog_var == var(prog_var_type).
:- type prog_varset == varset(prog_var_type).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type parse_error
    --->    error(string, int).

:- pred parse_items(list(item)::out, list(parse_error)::out, io::di, io::uo) is det.

%------------------------------------------------------------------------------%

:- implementation.

:- import_module parser.
:- import_module term_io.

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

:- pred parse_clause(varset::in, term::in, term::in, parse_result(clause)::out, io::di, io::uo) is det.

parse_clause(Varset, HeadTerm, BodyTerm, Result, !IO) :-
    parse_clause_head(Varset, HeadTerm, HeadResult, !IO),
    ( HeadResult = ok({Name, Vars}),
        parse_clause_body(BodyTerm, BodyResult, !IO),
        ( BodyResult = ok(BodyGoal),
            Result = ok(clause(Name, Vars, BodyGoal, coerce(Varset)))
        ; BodyResult = error(Errors),
            Result = error(Errors)
        )
    ; HeadResult = error(Errors),
        Result = error(Errors)
    ).

:- pred parse_clause_head(varset::in, term::in, parse_result({string, list(prog_var)})::out, io::di, io::uo) is det.

parse_clause_head(_Varset, HeadTerm, Result, !IO) :-
    (
            % XXX Need to handle functors in the head arguments.
        HeadTerm = term.functor(term.atom(Name), HeadArgs, _HeadContext),
        prog_var_list(HeadArgs, HeadVars)
    ->
        Result = ok({Name, HeadVars})
    ;
        Result = error([error("XXX", 0)])
    ).

:- pred prog_var_list(list(term)::in, list(prog_var)::out) is semidet.

prog_var_list([], []).
prog_var_list([Term | Terms], [ProgVar | ProgVars]) :-
    Term = variable(Var, _),
    coerce_var(Var, ProgVar),
    prog_var_list(Terms, ProgVars).

:- pred parse_clause_body(term::in, parse_result(hlds_goal)::out, io::di, io::uo) is det.

parse_clause_body(functor(Const, Args, _Context), Result, !IO) :-
    ( Const = atom(Atom) ->
            % Parse a conjunction
        ( Atom = ",", Args = [TermA, TermB] ->
                % XXX Flatten conjunctions?
            parse_clause_body(TermA, ResultA, !IO),
            ( ResultA = ok(GoalA),
                parse_clause_body(TermB, ResultB, !IO),
                ( ResultB = ok(GoalB),
                    Result = ok(conj([GoalA, GoalB]))
                ; ResultB = error(Errors),
                    Result = error(Errors)
                )
            ; ResultA = error(Errors),
                Result = error(Errors)
            )
            % Parse a unification
        ; Atom = "=", Args = [TermA, TermB] ->
            ( TermA = variable(VarA, _ContextA),
                ProgVarA = coerce_var(VarA),
                ( TermB = variable(VarB, _ContextB),
                    Result = ok(unify(ProgVarA, rhs_var(coerce_var(VarB))))
                ; TermB = functor(ConstB, ArgsB, _ContextB),
                    ( ConstB = atom(AtomB),
                        ( prog_var_list(ArgsB, VarsB) ->
                            Result = ok(unify(ProgVarA, rhs_functor(cons(AtomB), VarsB)))
                        ;
                            Result = error([error("Not a var list in the unify", 0)])
                        )
                    ; ConstB = integer(IntB),
                        Result = ok(unify(ProgVarA, rhs_functor(int_const(IntB), [])))
                    ; ConstB = string(_StrB),
                        Result = error([error("string constant", 0)])
                    ; ConstB = float(_FloatB),
                        Result = error([error("float constant", 0)])
                    ; ConstB = implementation_defined(_),
                        Result = error([error("implementation_defined constant", 0)])
                    )
                )
            ; TermA = functor(_, _, _),
                Result = error([error("Unable to handle functor on LHS of unification", 0)])
            )
        ;
                % It's a call
            ( prog_var_list(Args, Vars) ->
                Result = ok(call(Atom, Vars))
            ;
                Result = error([error("call with non variable arguments", 0)])
            )
        )
    ;
        Result = error([error("expected an atom for the goal", 0)])
    ).
parse_clause_body(variable(_Var, _Context), Result, !IO) :-
    Result = error([error("unexpected variable", 0)]).

