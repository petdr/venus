:- module vc.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

main(!IO) :-
    io.write_string("hi.\n", !IO).
