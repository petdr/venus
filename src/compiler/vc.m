%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
:- module vc.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module error_util.
:- import_module hlds.
:- import_module make_hlds.
:- import_module parse_tree.
:- import_module sym_name.
:- import_module typecheck.

:- import_module list.

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    ( Args = [],
        io.write_string("Missing file name\n", !IO)
    ; Args = [FileName | _],
        ModuleName = file_name_to_module_name(FileName),
        io.see(FileName, SeeRes, !IO),
        ( SeeRes = ok,
            parse_items(FileName, Items, Errors, !IO),
            ( Errors = [],
                make_hlds(ModuleName, Items, HLDS0, !IO),
                front_end_pass(ErrorSpecs, HLDS0, HLDS),
                _ = HLDS,

                io.write(ErrorSpecs, !IO),
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

:- pred front_end_pass(list(error_spec)::out, hlds::in, hlds::out) is det.

front_end_pass(Errors, !HLDS) :-
    typecheck_hlds(Errors, !HLDS).
    

