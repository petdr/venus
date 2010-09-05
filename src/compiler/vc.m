:- module vc.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module make_hlds.
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
            ( Errors = [],
                make_hlds(Items, HLDS, !IO),

                io.write(HLDS, !IO),
                io.nl(!IO)
            ; Errors = [_|_],
                io.write(Errors, !IO),
                io.nl(!IO)
            )
        ; SeeRes = error(Err),
            io.write(Err, !IO),
            io.nl(!IO)
        )
    ).
