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
    read_chr_rule(_ : chr_io.read_result(chr_rule), !IO),
    read_chr_goal(Result, !IO),
    ( Result = ok({Varset, Goal}),
        solutions(solve([], Varset, Goal), Solutions),
        list.foldl(output_solution(Varset), Solutions, !IO),
        io.nl(!IO)
    ; Result = error(Context, Err),
        io.write(Context, !IO),
        io.write_string(" ", !IO),
        io.write_string(Err, !IO),
        io.nl(!IO)
    ; Result = eof,
        true
    ).
    
:- pred output_solution(varset::in, list(constraint)::in, io::di, io::uo) is det.

output_solution(Varset, Constraints, !IO) :-
    io.write_string("\n*** Solution ***\n", !IO),
    list.foldl(output(Varset), Constraints, !IO).

:- pred output(varset::in, constraint::in, io::di, io::uo) is det.

output(Varset, Constraint, !IO) :-
    output_constraint(Varset, Constraint, !IO),
    io.nl(!IO).
