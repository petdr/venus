%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%
:- module chr_io.
:- interface.

:- import_module chr.

:- import_module io.
:- import_module term.
:- import_module varset.

%------------------------------------------------------------------------------%

:- type read_result(T)
    --->    ok(T)
    ;       eof
    ;       error(term.context, string)
    .

:- type goal_or_rule(T)
    --->    goal(varset(T), chr_goal(T))
    ;       rule(chr_rule(T))
    .

:- pred read_chr(chr_io.read_result(goal_or_rule(T))::out, io::di, io::uo) is det.

:- pred read_chr_goal(chr_io.read_result({varset(T), chr_goal(T)})::out, io::di, io::uo) is det.

:- pred read_chr_rule(chr_io.read_result(chr_rule(T))::out, io::di, io::uo) is det.

%------------------------------------------------------------------------------%

:- type parse_result(T)
    --->    ok(T)
    ;       error(term.context, string)
    .

:- pred parse_chr_goal(term(T)::in, parse_result(chr_goal(T))::out) is det.

:- pred parse_chr_rule(varset(T)::in, term(T)::in, parse_result(chr_rule(T))::out) is det.

%------------------------------------------------------------------------------%

:- pred output_constraint(varset(T)::in, constraint(T)::in, io::di, io::uo) is det.

:- pred output_chr_goal(varset(T)::in, chr_goal(T)::in, io::di, io::uo) is det.

    % Take a constraint and flatten all the disjunctions and conjunctions.
:- func flatten(chr_goal(T)) = chr_goal(T).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module list.
:- import_module ops.
:- import_module parser.
:- import_module term_io.

read_chr(Result, !IO) :-
    parser.read_term_with_op_table(chr_op_table, ReadResult, !IO),
    ( ReadResult = term(Varset, Term),
        parse_chr_rule(Varset, Term, RuleResult),
        ( RuleResult = ok(Rule),
            Result = ok(rule(Rule))
        ; RuleResult = error(_, _),
            parse_chr_goal(Term, GoalResult),
            ( GoalResult = ok(Goal),
                Result = ok(goal(Varset, Goal))
            ; GoalResult = error(C, Err),
                Result = error(C, Err)
            )
        )
    ; ReadResult = error(Err, Int),
        io.input_stream_name(File, !IO),
        Result = error(context(File, Int), Err)
    ; ReadResult = eof,
        Result = eof
    ).


read_chr_goal(Result, !IO) :-
    parser.read_term_with_op_table(chr_op_table, ReadResult, !IO),
    ( ReadResult = term(Varset, Term),
        parse_chr_goal(Term, GoalResult),
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
    ( ReadResult = term(Varset, Term),
        parse_chr_rule(Varset, Term, RuleResult),
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

parse_chr_goal(variable(_V, C), error(C, "Unexpected variable")).
parse_chr_goal(functor(Const, Args, Context), Result) :-
    ( Const = atom(","), Args = [TermA, TermB] ->
        parse_chr_goal(TermA, ResultA),
        parse_chr_goal(TermB, ResultB),
        Result = combine_results(to_conj, ResultA, ResultB)
    ; Const = atom(";"), Args = [TermA, TermB] ->
        parse_chr_goal(TermA, ResultA),
        parse_chr_goal(TermB, ResultB),
        Result = combine_results(to_disj, ResultA, ResultB)
    ; Const = atom("true"), Args = [] ->
        Result = ok(builtin(true))
    ; Const = atom("fail"), Args = [] ->
        Result = ok(builtin(fail))
    ; Const = atom("="), Args = [TermA, TermB] ->
        Result = ok(builtin(unify(TermA, TermB)))
    ; Const = atom(Name) ->
        Result = ok(chr(chr(Name, Args)))
    ;
        Result = error(Context, "unknown term")
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

parse_chr_rule(_Varset, variable(_V, C), error(C, "Unexpected variable")).
parse_chr_rule(Varset, Term @ functor(Const, Args, _Context), Result) :-
    ( Const = atom("@"), Args = [RuleName, Rule0] ->
        parse_rule_name(RuleName, ResultA),
        Rule = Rule0
    ;
        ResultA = ok(no_name),
        Rule = Term
    ),
    parse_rule(Rule, ResultB),
    Result = combine_results(to_chr_rule(Varset), ResultA, ResultB).

:- pred parse_rule_name(term(T)::in, parse_result(chr_name)::out) is det.

parse_rule_name(variable(_V, C), error(C, "Unexpected variable")).
parse_rule_name(functor(Const, Args, Context), Result) :-
    ( Const = atom(Name), Args = [] ->
        Result = ok(name(Name))
    ;
        Result = error(Context, "Expected rule name")
    ).
    
:- func to_chr_rule(varset(T), chr_name, unnamed_rule(T)) = chr_rule(T).

to_chr_rule(Varset, Name, {Prop, Simp, Guard, Body}) = chr_rule(Name, Prop, Simp, Guard, Body, Varset).

:- type unnamed_rule(T) == {chr_constraints(T), chr_constraints(T), builtin_constraints(T), constraints(T)}.

:- pred parse_rule(term(T)::in, parse_result(unnamed_rule(T))::out) is det.  
parse_rule(variable(_V, C), error(C, "Unexpected variable")).
parse_rule(functor(Const, Args, Context), Result) :-
    ( Const = atom("<=>"), Args = [TermA, TermB] ->
        parse_simpgation_rule_head(TermA, ResultA),
        parse_guarded_rhs(TermB, ResultB),
        Result = combine_results(to_simp_rule, ResultA, ResultB)
    ; Const = atom("==>"), Args = [TermA, TermB] ->
        parse_conj(parse_chr_constraint, TermA, ResultA),
        parse_guarded_rhs(TermB, ResultB),
        Result = combine_results(to_prop_rule, ResultA, ResultB)
    ;
        Result = error(Context, "Expected <=> or ==>")
    ).

:- func to_simp_rule({chr_constraints(T), chr_constraints(T)}, {builtin_constraints(T), constraints(T)}) = unnamed_rule(T).

to_simp_rule({Prop, Simp}, {Guard, Body}) = {Prop, Simp, Guard, Body}.

:- func to_prop_rule(chr_constraints(T), {builtin_constraints(T), constraints(T)}) = unnamed_rule(T).

to_prop_rule(Prop, {Guard, Body}) = {Prop, [], Guard, Body}.

:- pred parse_simpgation_rule_head(term(T)::in, parse_result({chr_constraints(T), chr_constraints(T)})::out) is det.

parse_simpgation_rule_head(variable(_V, C), error(C, "Unexpected variable")).
parse_simpgation_rule_head(Term @ functor(Const, Args, _Context), Result) :-
    ( Const = atom("\\"), Args = [TermA, TermB] ->
        parse_conj(parse_chr_constraint, TermA, ResultA),
        SimpTerm = TermB
    ;
        ResultA = ok([]),
        SimpTerm = Term
    ),
    parse_conj(parse_chr_constraint, SimpTerm, ResultB),
    Result = combine_results(func(A, B) = {A, B}, ResultA, ResultB).

:- pred parse_guarded_rhs(term(T)::in, parse_result({builtin_constraints(T), constraints(T)})::out) is det.

parse_guarded_rhs(variable(_V, C), error(C, "Unexpected variable")).
parse_guarded_rhs(Term @ functor(Const, Args, _Context), Result) :-
    ( Const = atom("|"), Args = [TermA, TermB] ->
        parse_conj(parse_builtin_constraint, TermA, ResultA),
        ConstraintsTerm = TermB
    ;
        ResultA = ok([]),
        ConstraintsTerm = Term
    ),
    parse_conj(parse_constraint, ConstraintsTerm, ResultB),
    Result = combine_results(func(A, B) = {A, B}, ResultA, ResultB).

:- pred parse_conj(pred(term(T), parse_result(U))::pred(in, out) is det, term(T)::in, parse_result(list(U))::out) is det.

parse_conj(_ParseOneItem, variable(_V, C), error(C, "Unexpected variable")).
parse_conj(ParseOneItem, Term @ functor(Const, Args, _Context), Result) :-
    ( Const = atom(","), Args = [TermA, TermB] ->
        parse_conj(ParseOneItem, TermA, ResultA),
        parse_conj(ParseOneItem, TermB, ResultB),
        Result = combine_results(list.append, ResultA, ResultB)
    ;
        ParseOneItem(Term, Result0),
        Result = combine_results(list.cons, Result0, ok([]))
    ).

:- pred parse_constraint(term(T)::in, parse_result(constraint(T))::out) is det.

parse_constraint(Term, Result) :-
    parse_builtin_constraint(Term, ResultBuiltin),
    ( ResultBuiltin = ok(Builtin),
        Result = ok(builtin(Builtin))
    ; ResultBuiltin = error(_, _),
        parse_chr_constraint(Term, ResultChr),
        ( ResultChr = ok(Chr),
            Result = ok(chr(Chr))
        ; ResultChr = error(C, Err),
            Result = error(C, Err)
        )
    ).

:- pred parse_chr_constraint(term(T)::in, parse_result(chr_constraint(T))::out) is det.

parse_chr_constraint(variable(_V, C), error(C, "Unexpected variable")).
parse_chr_constraint(functor(Const, Args, Context), Result) :-
    ( Const = atom(Name) ->
        Result = ok(chr(Name, Args))
    ;
        Result = error(Context, "expected atom with possibly arguments")
    ).

:- pred parse_builtin_constraint(term(T)::in, parse_result(builtin_constraint(T))::out) is det.

parse_builtin_constraint(variable(_V, C), error(C, "Unexpected variable")).
parse_builtin_constraint(functor(Const, Args, Context), Result) :-
    ( Const = atom("true"), Args = [] ->
        Result = ok(true)
    ; Const = atom("fail"), Args = [] ->
        Result = ok(fail)
    ; Const = atom("="), Args = [TermA, TermB] ->
        Result = ok(unify(TermA, TermB))
    ; Const = atom("not"), Args = [TermA] ->
        parse_builtin_constraint(TermA, ResultA),
        ( ResultA = ok(BuiltinA),
            Result = ok(not(BuiltinA))
        ; ResultA = error(_, _),
            Result = ResultA
        )
    ;
        Result = error(Context, "unknown builtin constraint")
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

:- func combine_results(func(T, U) = V, parse_result(T), parse_result(U)) = parse_result(V).

combine_results(Combine, ok(A), ok(B)) = ok(Combine(A, B)).
combine_results(_, ok(_), error(C, B)) = error(C, B).
combine_results(_, error(C, A), _) = error(C, A).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

output_constraint(Varset, chr(chr(Name, Args)), !IO) :-
    Term = functor(atom(Name), Args, context_init),
    term_io.write_term(Varset, Term, !IO).
output_constraint(Varset, builtin(unify(TermA, TermB)), !IO) :-
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" = ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_constraint(Varset, builtin(equals(TermA, TermB)), !IO) :-
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" == ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_constraint(_Varset, builtin(true), !IO) :-
    io.write_string("true", !IO).
output_constraint(_Varset, builtin(fail), !IO) :-
    io.write_string("fail", !IO).
output_constraint(Varset, builtin(not(B)), !IO) :-
    io.write_string("not(", !IO),
    output_constraint(Varset, builtin(B), !IO),
    io.write_string(")", !IO).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

output_chr_goal(Varset, Constraint, !IO) :-
    output_chr_goal_2(0, Varset, flatten(Constraint), !IO),
    io.nl(!IO).

%------------------------------------------------------------------------------%

:- pred output_chr_goal_2(int::in, varset(T)::in, chr_goal(T)::in, io::di, io::uo) is det.

output_chr_goal_2(Indent, Varset, conj(Cs), !IO) :-
    ( Cs = [],
        output_indent(Indent, !IO),
        io.write_string("true", !IO)
    ; Cs = [H | T],
        output_chr_goal_2(Indent, Varset, H, !IO),
        output_chr_goal_list(Indent, Varset, conj_sep, T, !IO)
    ).
output_chr_goal_2(Indent, Varset, disj(Cs), !IO) :-
    ( Cs = [],
        output_indent(Indent, !IO),
        io.write_string("fail", !IO)
    ; Cs = [H|T],
        output_indent(Indent, !IO),
        io.write_string("(", !IO),
        output_chr_goal_2(Indent + 1, Varset, H, !IO),
        output_chr_goal_list(Indent + 1, Varset, disj_sep, T, !IO),
        output_indent(Indent, !IO),
        io.write_string(")", !IO)
    ).
output_chr_goal_2(Indent, Varset, builtin(not(B)), !IO) :-
    output_indent(Indent, !IO),
    io.write_string("not(", !IO),
    output_chr_goal_2(Indent, Varset, builtin(B), !IO),
    io.write_string(")", !IO).
output_chr_goal_2(Indent, _Varset, builtin(fail), !IO) :-
    output_indent(Indent, !IO),
    io.write_string("true", !IO).
output_chr_goal_2(Indent, _Varset, builtin(true), !IO) :-
    output_indent(Indent, !IO),
    io.write_string("true", !IO).
output_chr_goal_2(Indent, Varset, builtin(equals(TermA, TermB)), !IO) :-
    output_indent(Indent, !IO),
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" == ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_chr_goal_2(Indent, Varset, builtin(unify(TermA, TermB)), !IO) :-
    output_indent(Indent, !IO),
    term_io.write_term(Varset, TermA, !IO),
    io.write_string(" = ", !IO),
    term_io.write_term(Varset, TermB, !IO).
output_chr_goal_2(Indent, Varset, chr(chr(Name, Args)), !IO) :-
    output_indent(Indent, !IO),
    term_io.write_term(Varset, functor(atom(Name), Args, context_init), !IO).

%------------------------------------------------------------------------------%

:- type sep
    --->    conj_sep
    ;       disj_sep
    .

:- pred output_chr_goal_list(int::in, varset(T)::in, sep::in, list(chr_goal(T))::in, io::di, io::uo) is det.

output_chr_goal_list(_Indent, _Varset, _Sep, [], !IO).
output_chr_goal_list(Indent, Varset, Sep, [C | Cs], !IO) :-
    ( Sep = conj_sep,
        io.write_string(",", !IO)
    ; Sep = disj_sep,
        output_indent(Indent - 1, !IO),
        io.write_string(";", !IO)
    ),
    output_chr_goal_2(Indent, Varset, C, !IO),
    output_chr_goal_list(Indent, Varset, Sep, Cs, !IO).

%------------------------------------------------------------------------------%

:- pred output_indent(int::in, io::di, io::uo) is det.

output_indent(N, !IO) :-
    io.nl(!IO),
    output_indent_2(N, !IO).

:- pred output_indent_2(int::in, io::di, io::uo) is det.

output_indent_2(N, !IO) :-
    ( N > 0 ->
        io.write_string(" ", !IO),
        output_indent_2(N - 1, !IO)
    ;
        true
    ).

%------------------------------------------------------------------------------%
%------------------------------------------------------------------------------%

flatten(conj(Gs)) = conj(list.reverse(list.foldl(flatten_conj, Gs, []))).
flatten(disj(Gs)) = disj(list.reverse(list.foldl(flatten_disj, Gs, []))).
flatten(C @ builtin(_)) = C.
flatten(C @ chr(_)) = C.

:- func flatten_conj(chr_goal(T), list(chr_goal(T))) = list(chr_goal(T)).

flatten_conj(C0, !.Gs) = !:Gs :-
    C = flatten(C0),
    ( C = conj(Cs) ->
        list.append(Cs, !Gs)
    ;
        list.append([C], !Gs)
    ).

:- func flatten_disj(chr_goal(T), list(chr_goal(T))) = list(chr_goal(T)).

flatten_disj(C0, !.Gs) = !:Gs :-
    C = flatten(C0),
    ( C = disj(Cs) ->
        list.append(Cs, !Gs)
    ;
        list.append([C], !Gs)
    ).

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
