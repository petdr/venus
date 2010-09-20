%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
:- module compiler_util.

:- interface.

:- func sorry(string::in, string::in) = (T::out) is erroneous.
:- pred sorry(string::in, string::in) is erroneous.

:- func unexpected(string::in, string::in) = (T::out) is erroneous.
:- pred unexpected(string::in, string::in) is erroneous.

:- implementation.

:- import_module list.
:- import_module require.
:- import_module string.

    % Call error/1 with a "Sorry, not implemented" message.
    %
sorry(Module, What) = _ :- sorry(Module, What).
sorry(Module, What) :-
    string.format("%s: Sorry, not implemented: %s", [s(Module), s(What)], ErrorMessage),
    error(ErrorMessage).

unexpected(Module, What) = _ :- unexpected(Module, What).
unexpected(Module, What) :-
    string.format("%s: Unexpected: %s", [s(Module), s(What)], ErrorMessage),
    error(ErrorMessage).
