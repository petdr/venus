%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module chr_io.
:- interface.

:- import_module chr.

:- import_module io.
:- import_module term.
:- import_module varset.

:- type read_result(T)
    --->    ok(T)
    ;       eof
    ;       error(term.context, string)
    .

:- pred read_chr_goal(chr_io.read_result({varset(T), chr_goal(T)})::out, io::di, io::uo) is det.

:- pred read_chr_rule(chr_io.read_result(chr_rule(T))::out, io::di, io::uo) is det.

%------------------------------------------------------------------------------%

:- pred output_constraint(varset(T)::in, constraint(T)::in, io::di, io::uo) is det.

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module list.
:- import_module ops.
:- import_module parser.
:- import_module term_io.

read_chr_goal(Result, !IO) :-
    parser.read_term_with_op_table(chr_op_table, ReadResult, !IO),
    ( ReadResult = term(Varset, Term),
        parse_goal(Term, GoalResult),
        ( GoalResult = ok(Goal),
            Result = ok({Varset, Goal})
        ; GoalResult = error(Context, Err),
            Result = error(Context, Err)
        )
    ; ReadResult = error(Err, Int),
        io.input_stream_name(File, !IO),
        Result = error(context(File, Int), Err)
    ; ReadResult = eof,
        Result = eof
    ).

read_chr_rule(Result, !IO) :-
    parser.read_term_with_op_table(chr_op_table, ReadResult, !IO),
    ( ReadResult = term(_Varset, Term),
        parse_rule(Term, RuleResult),
        ( RuleResult = ok(Rule),
            Result = ok(Rule)
        ; RuleResult = error(Context, Err),
            Result = error(Context, Err)
        )
    ; ReadResult = error(Err, Int),
        io.input_stream_name(File, !IO),
        Result = error(context(File, Int), Err)
    ; ReadResult = eof,
        Result = eof
    ).

%------------------------------------------------------------------------------%

:- type parse_result(T)
    --->    ok(T)
    ;       error(term.context, string)
    .

:- pred parse_goal(term(T)::in, parse_result(chr_goal(T))::out) is det.

parse_goal(variable(_V, C), error(C, "Unexpected variable")).
parse_goal(functor(Const, Args, Context), Result) :-
    ( Const = atom(","), Args = [TermA, TermB] ->
        parse_goal(TermA, ResultA),
        parse_goal(TermB, ResultB),
        Result = combine_result(to_conj, ResultA, ResultB)
    ; Const = atom(";"), Args = [TermA, TermB] ->
        parse_goal(TermA, ResultA),
        parse_goal(TermB, ResultB),
        Result = combine_result(to_disj, ResultA, ResultB)
    ; Const = atom("true"), Args = [] ->
        Result = ok(builtin(true))
    ; Const = atom("fail"), Args = [] ->
        Result = ok(builtin(fail))
    ; Const = atom("="), Args = [TermA, TermB] ->
        Result = ok(builtin(unify(TermA, TermB)))
    ;
        Result = error(Context, "Unknown term")
    ).

:- func to_conj(chr_goal(T), chr_goal(T)) = chr_goal(T).

to_conj(GoalA, GoalB) = conj(Goals) :-
    ( GoalA = conj(GAs) ->
        ( GoalB = conj(GBs) -> Goals = GAs ++ GBs ; Goals = GAs ++ [GoalB])
    ;
        ( GoalB = conj(GBs) -> Goals = [GoalA | GBs] ; Goals = [GoalA, GoalB])
    ).

:- func to_disj(chr_goal(T), chr_goal(T)) = chr_goal(T).

to_disj(GoalA, GoalB) = disj(Goals) :-
    ( GoalA = disj(GAs) ->
        ( GoalB = disj(GBs) -> Goals = GAs ++ GBs ; Goals = GAs ++ [GoalB])
    ;
        ( GoalB = disj(GBs) -> Goals = [GoalA | GBs] ; Goals = [GoalA, GoalB])
    ).
        
%------------------------------------------------------------------------------%

:- pred parse_rule(term(T)::in, parse_result(chr_rule(T))::out) is det.

parse_rule(Term, Result) :-
    Result = error(get_term_context(Term), "XXX").

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func combine_result(func(T, U) = V, parse_result(T), parse_result(U)) = parse_result(V).

combine_result(Combine, ok(A), ok(B)) = ok(Combine(A, B)).
combine_result(_, ok(_), error(C, B)) = error(C, B).
combine_result(_, error(C, A), _) = error(C, A).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

output_constraint(Varset, chr(chr(Name, Args)), !IO) :-
    Term = functor(atom(Name), Args, context_init),
    term_io.write_term(Varset, Term, !IO).
output_constraint(Varset, builtin(unify(TermA, TermB)), !IO) :-
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" = ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_constraint(_Varset, builtin(true), !IO) :-
    io.write_string("true", !IO).
output_constraint(_Varset, builtin(fail), !IO) :-
    io.write_string("fail", !IO).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- type chr_op_table ---> chr_op_table.

:- pred ops_table(string::in, op_info::out, list(op_info)::out) is semidet.
  
ops_table("=", op_info(infix(x, x), 700), []).
ops_table(",", op_info(infix(x, y), 1000), []).
ops_table(";", op_info(infix(x, y), 1100), []).
ops_table("\\", op_info(infix(x, x), 1101), []).
ops_table("|", op_info(infix(x, x), 1101), []).
ops_table("<=>",  op_info(infix(x, x), 1102), []).
ops_table("==>",  op_info(infix(x, x), 1102), []).
ops_table("@",  op_info(infix(x, x), 1103), []).

:- instance ops.op_table(chr_op_table) where [
    
    ( ops.lookup_infix_op(_, Op, Priority, LeftAssoc, RightAssoc) :-
        ops_table(Op, Info, _),
        Info = op_info(infix(LeftAssoc, RightAssoc), Priority)
    ),

    ops.lookup_operator_term(_, _, _, _) :- fail,

    ( ops.lookup_prefix_op(_, Op, Priority, LeftAssoc) :-
        ops_table(Op, _, OtherInfo),
        OtherInfo = [op_info(prefix(LeftAssoc), Priority)]
    ),

    ops.lookup_postfix_op(_, _, _, _) :- fail,
    ops.lookup_binary_prefix_op(_, _, _, _, _) :- fail,

    ops.lookup_op(Table, Op) :- ops.lookup_infix_op(Table, Op, _, _, _),
    ops.lookup_op(Table, Op) :- ops.lookup_prefix_op(Table, Op, _, _),
    ops.lookup_op(Table, Op) :- ops.lookup_binary_prefix_op(Table, Op, _, _, _),
    ops.lookup_op(Table, Op) :- ops.lookup_postfix_op(Table, Op, _, _),
    
    ops.lookup_op_infos(_, Op, OpInfo, OtherInfos) :-
        ops_table(Op, OpInfo, OtherInfos),

    ops.max_priority(_) = 1103,
    ops.arg_priority(Table) = ops.max_priority(Table) + 1
].

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
