:- module vc.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module parse_tree.

:- import_module list.

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    ( Args = [],
        io.write_string("Missing file name\n", !IO)
    ; Args = [FileName | _],
        io.see(FileName, SeeRes, !IO),
        ( SeeRes = ok,
            parse_items(Items, Errors, !IO),
            io.write(Items, !IO),
            io.nl(!IO),
            io.write(Errors, !IO),
            io.nl(!IO)
        ; SeeRes = error(Err),
            io.write(Err, !IO),
            io.nl(!IO)
        )
    ).
