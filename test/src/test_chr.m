:- module test_chr.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module chr.
:- import_module chr_io.

:- import_module list.
:- import_module solutions.
:- import_module varset.

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    ( Args = [File | _] ->
        io.see(File, _, !IO)
    ;
        true
    ),
    main_2([], _Rules, !IO).

:- pred main_2(list(chr_rule)::in, list(chr_rule)::out, io::di, io::uo) is det.

main_2(!Rules, !IO) :-
    read_chr(Result, !IO),
    ( Result = ok(GoalOrRule),
        ( GoalOrRule = goal(Varset, Goal),
            io.write_string("\nExecuting goal\n", !IO),
            solutions(solve(!.Rules, Varset, Goal), Solutions),
            list.foldl(output_solution(Varset), Solutions, !IO),
            io.nl(!IO)
        ; GoalOrRule = rule(_Varset, Rule),
            list.cons(Rule, !Rules)
        ),
        main_2(!Rules, !IO)
    ; Result = eof,
        true
    ; Result = error(Context, Err),
        io.write(Context, !IO),
        io.write_string(" ", !IO),
        io.write_string(Err, !IO),
        io.nl(!IO),
        main_2(!Rules, !IO)
    ).



    
:- pred output_solution(varset::in, list(constraint)::in, io::di, io::uo) is det.

output_solution(Varset, Constraints, !IO) :-
    io.write_string("*** Solution ***\n", !IO),
    list.foldl(output(Varset), Constraints, !IO).

:- pred output(varset::in, constraint::in, io::di, io::uo) is det.

output(Varset, Constraint, !IO) :-
    output_constraint(Varset, Constraint, !IO),
    io.nl(!IO).
