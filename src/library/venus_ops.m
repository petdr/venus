%---------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%---------------------------------------------------------------------------%
% Copyright (C) 1995-2008 The University of Melbourne.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File: venus_ops.m.
% Main author: fjh.
% Stability: low.
% 
% This module exports a typeclass `venus_ops.op_table' which is used to define
% operator precedence tables for use by `parser.read_term_with_op_table'
% and `term_io.write_term_with_op_table'.
%
% It also exports an instance `venus_ops.venus_op_table' that implements the
% Mercury operator table defined in the Mercury Language Reference Manual.
%
% See samples/calculator2.m for an example program.
%
% XXX In the current implementation the table of Mercury operators
% is fixed and cannot be modified at run-time.
% 
%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- module venus_ops.
:- interface.

:- import_module ops.

%-----------------------------------------------------------------------------%

    % The table of Mercury operators.
    % See the "Builtin Operators" section of the "Syntax" chapter
    % of the Mercury Language Reference Manual for details.
    %
:- type venus_ops.venus_op_table.
:- instance ops.op_table(venus_ops.venus_op_table).

:- func venus_ops.init_venus_op_table = (venus_ops.venus_op_table::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

% Anything below here is not documented in the library reference manual.

:- interface.

%
% For use by parser.m, term_io.m, stream.string_writer.m.
%

:- pred adjust_priority_for_assoc(ops.priority::in, ops.assoc::in,
    ops.priority::out) is det.

:- func venus_ops.venus_max_priority(venus_op_table) = ops.priority.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module list.

:- type venus_ops.venus_op_table
    --->    venus_ops.venus_op_table.

venus_ops.init_venus_op_table = venus_ops.venus_op_table.

:- instance ops.op_table(venus_ops.venus_op_table) where [
    pred(ops.lookup_infix_op/5) is venus_ops.lookup_venus_infix_op,
    pred(ops.lookup_prefix_op/4) is venus_ops.lookup_venus_prefix_op,
    pred(ops.lookup_binary_prefix_op/5) is venus_ops.lookup_venus_binary_prefix_op,
    pred(ops.lookup_postfix_op/4) is venus_ops.lookup_venus_postfix_op,
    pred(ops.lookup_op/2) is venus_ops.lookup_venus_op,
    pred(ops.lookup_op_infos/4) is venus_ops.lookup_venus_op_infos,
    pred(ops.lookup_operator_term/4) is venus_ops.lookup_venus_operator_term,
    func(ops.max_priority/1) is venus_ops.venus_max_priority,
    func(ops.arg_priority/1) is venus_ops.venus_arg_priority
].

:- pred venus_ops.lookup_venus_infix_op(venus_op_table::in, string::in,
    ops.priority::out, ops.assoc::out, ops.assoc::out) is semidet.

venus_ops.lookup_venus_infix_op(_OpTable, Name, Priority,
        LeftAssoc, RightAssoc) :-
    venus_ops.op_table(Name, Info, MaybeOtherInfo),
    (
        Info = op_info(Class, PriorityPrime),
        Class = infix(LeftAssocPrime, RightAssocPrime)
    ->
        LeftAssoc = LeftAssocPrime,
        RightAssoc = RightAssocPrime,
        Priority = PriorityPrime
    ;
        MaybeOtherInfo = [op_info(Class, PriorityPrime)],
        Class = infix(LeftAssocPrime, RightAssocPrime)
    ->
        LeftAssoc = LeftAssocPrime,
        RightAssoc = RightAssocPrime,
        Priority = PriorityPrime
    ;
        fail
    ).

:- pred venus_ops.lookup_venus_prefix_op(venus_op_table::in,
    string::in, ops.priority::out, ops.assoc::out) is semidet.

venus_ops.lookup_venus_prefix_op(_OpTable, Name, Priority, LeftAssoc) :-
    venus_ops.op_table(Name, Info, MaybeOtherInfo),
    ( Info = op_info(prefix(LeftAssocPrime), PriorityPrime) ->
        LeftAssoc = LeftAssocPrime,
        Priority = PriorityPrime
    ; MaybeOtherInfo = [op_info(prefix(LeftAssocPrime), PriorityPrime)] ->
        LeftAssoc = LeftAssocPrime,
        Priority = PriorityPrime
    ;
        fail
    ).

:- pred venus_ops.lookup_venus_binary_prefix_op(venus_op_table::in, string::in,
    ops.priority::out, ops.assoc::out, ops.assoc::out) is semidet.

venus_ops.lookup_venus_binary_prefix_op(_OpTable, Name, Priority,
        LeftAssoc, RightAssoc) :-
    venus_ops.op_table(Name, Info, MaybeOtherInfo),
    (
        Info = op_info(Class, PriorityPrime),
        Class = binary_prefix(LeftAssocPrime, RightAssocPrime)
    ->
        LeftAssoc = LeftAssocPrime,
        RightAssoc = RightAssocPrime,
        Priority = PriorityPrime
    ;
        MaybeOtherInfo = [op_info(Class, PriorityPrime)],
        Class = binary_prefix(LeftAssocPrime, RightAssocPrime)
    ->
        LeftAssoc = LeftAssocPrime,
        RightAssoc = RightAssocPrime,
        Priority = PriorityPrime
    ;
        fail
    ).

:- pred venus_ops.lookup_venus_postfix_op(venus_op_table::in,
    string::in, ops.priority::out, ops.assoc::out) is semidet.

venus_ops.lookup_venus_postfix_op(_OpTable, Name, Priority, LeftAssoc) :-
    venus_ops.op_table(Name, Info, MaybeOtherInfo),
    ( Info = op_info(postfix(LeftAssocPrime), PriorityPrime) ->
        LeftAssoc = LeftAssocPrime,
        Priority = PriorityPrime
    ; MaybeOtherInfo = [op_info(postfix(LeftAssocPrime), PriorityPrime)] ->
        LeftAssoc = LeftAssocPrime,
        Priority = PriorityPrime
    ;
        fail
    ).

:- pred venus_ops.lookup_venus_op(venus_op_table::in, string::in) is semidet.

venus_ops.lookup_venus_op(_OpTable, Name) :-
    venus_ops.op_table(Name, _, _).

:- pred venus_ops.lookup_venus_op_infos(venus_op_table::in, string::in,
    op_info::out, list(op_info)::out) is semidet.

venus_ops.lookup_venus_op_infos(_OpTable, Name, Info, OtherInfos) :-
    venus_ops.op_table(Name, Info, OtherInfos).

:- pred venus_ops.lookup_venus_operator_term(venus_op_table::in,
    ops.priority::out, ops.assoc::out, ops.assoc::out) is det.

    % Left associative, lower priority than everything except record syntax.
venus_ops.lookup_venus_operator_term(_OpTable, 120, y, x).

venus_ops.venus_max_priority(_Table) = 1200.

:- func venus_ops.venus_arg_priority(venus_op_table) = ops.priority.

    % This needs to be less than the priority of the ','/2 operator.
venus_ops.venus_arg_priority(_Table) = 999.

:- pred venus_ops.op_table(string::in, op_info::out, list(op_info)::out) is semidet.

venus_ops.op_table(Op, Info, OtherInfos) :-
    % NOTE: Changes here may require changes to doc/reference_manual.texi.

    % (*) means that the operator is not useful in Mercury
    % and is provided only for compatibility.

    (
    % The following symbols represent more than one operator.
    % NOTE: The code of several other predicates above depends on the fact
    % that no symbol represents more than *two* operators, by assuming that
    % the length of OtherInfos cannot exceed one.

        Op = "+",
        Info = op_info(infix(y, x), 500),
        % standard ISO Prolog
        OtherInfos = [op_info(prefix(x), 500)]
        % traditional Prolog (not ISO)
    ;
        Op = "-",
        Info = op_info(infix(y, x), 500),
        % standard ISO Prolog
        OtherInfos = [op_info(prefix(x), 200)]
        % standard ISO Prolog
    ;
        Op = ":-",
        Info = op_info(infix(x, x), 1200),
        % standard ISO Prolog
        OtherInfos = [op_info(prefix(x), 1200)]
        % standard ISO Prolog
    ;
        Op = "^",
        Info = op_info(infix(x, y), 99),
        % ISO Prolog (prec. 200, bitwise xor), Mercury (record syntax)
        OtherInfos = [op_info(prefix(x), 100)]
        % Mercury extension (record syntax)
    ;
    % The remaining symbols all represent just one operator.

        % The following operators are standard ISO Prolog.
        ( Op = "*",     Info = op_info(infix(y, x), 400)
        ; Op = "**",    Info = op_info(infix(x, y), 200)
        ; Op = ",",     Info = op_info(infix(x, y), 1000)
        ; Op = "-->",   Info = op_info(infix(x, x), 1200)
        ; Op = "->",    Info = op_info(infix(x, y), 1050)
        ; Op = "/",     Info = op_info(infix(y, x), 400)
        ; Op = "//",    Info = op_info(infix(y, x), 400)
        ; Op = "/\\",   Info = op_info(infix(y, x), 500)
        ; Op = ";",     Info = op_info(infix(x, y), 1100)
        ; Op = "<",     Info = op_info(infix(x, x), 700)
        ; Op = "<<",    Info = op_info(infix(y, x), 400)
        ; Op = "=",     Info = op_info(infix(x, x), 700)
        ; Op = "=..",   Info = op_info(infix(x, x), 700)
        ; Op = "=:=",   Info = op_info(infix(x, x), 700)    % (*)
        ; Op = "=<",    Info = op_info(infix(x, x), 700)
        ; Op = "==",    Info = op_info(infix(x, x), 700)    % (*)
        ; Op = "=\\=",  Info = op_info(infix(x, x), 700)    % (*)
        ; Op = ">",     Info = op_info(infix(x, x), 700)
        ; Op = ">=",    Info = op_info(infix(x, x), 700)
        ; Op = ">>",    Info = op_info(infix(y, x), 400)
        ; Op = "?-",    Info = op_info(prefix(x), 1200)     % (*)
        ; Op = "@<",    Info = op_info(infix(x, x), 700)
        ; Op = "@=<",   Info = op_info(infix(x, x), 700)
        ; Op = "@>",    Info = op_info(infix(x, x), 700)
        ; Op = "@>=",   Info = op_info(infix(x, x), 700)
        ; Op = "\\",    Info = op_info(prefix(x), 200)
        ; Op = "\\+",   Info = op_info(prefix(y), 900)
        ; Op = "\\/",   Info = op_info(infix(y, x), 500)
        ; Op = "\\=",   Info = op_info(infix(x, x), 700)
        ; Op = "\\==",  Info = op_info(infix(x, x), 700)    % (*)
        ; Op = "div",   Info = op_info(infix(y, x), 400)
        ; Op = "is",    Info = op_info(infix(x, x), 701)    % ISO: prec 700
        ; Op = "mod",   Info = op_info(infix(x, x), 400)
        ; Op = "rem",   Info = op_info(infix(x, x), 400)
        ),
        OtherInfos = []
    ;
        % The following operator is a Goedel extension.
        Op = "~",       Info = op_info(prefix(y), 900),     % (*)
        OtherInfos = []
    ;
        % The following operators are NU-Prolog extensions.
        ( Op = "~=",    Info = op_info(infix(x, x), 700)    % (*)
        ; Op = "and",   Info = op_info(infix(x, y), 720)
        ; Op = "extends", Info = op_info(infix(x, x), 1150)   % (*)
        ; Op = "or",    Info = op_info(infix(x, y), 740)
        ; Op = "rule",  Info = op_info(prefix(x), 1199)
        ; Op = "when",  Info = op_info(infix(x, x), 900)    % (*)
        ; Op = "where", Info = op_info(infix(x, x), 1175)   % (*)
        ),
        OtherInfos = []
    ;
        % The following operators are Mercury/NU-Prolog extensions.
        ( Op = "<=",    Info = op_info(infix(x, y), 920)
        ; Op = "<=>",   Info = op_info(infix(x, y), 920)
        ; Op = "=>",    Info = op_info(infix(x, y), 920)
        ; Op = "all",   Info = op_info(binary_prefix(x, y), 950)
        ; Op = "some",  Info = op_info(binary_prefix(x, y), 950)
        ; Op = "if",    Info = op_info(prefix(x), 1160)
        ; Op = "then",  Info = op_info(infix(x, x), 1150)
        ; Op = "else",  Info = op_info(infix(x, y), 1170)
        ; Op = "catch", Info = op_info(infix(x, y), 1180)
        ; Op = "catch_any", Info = op_info(infix(x, y), 1190)
        ; Op = "not",   Info = op_info(prefix(y), 900)
        ; Op = "pred",  Info = op_info(prefix(x), 800)
        ),
        OtherInfos = []
    ;
        % The following operators are Mercury extensions.
        ( Op = "!",                 Info = op_info(prefix(x), 40)
        ; Op = "!.",                Info = op_info(prefix(x), 40)
        ; Op = "!:",                Info = op_info(prefix(x), 40)
        ; Op = "&",                 Info = op_info(infix(x, y), 1025)
        ; Op = "++",                Info = op_info(infix(x, y), 500)
        ; Op = "--",                Info = op_info(infix(y, x), 500)
        ; Op = "--->",              Info = op_info(infix(x, y), 1179)
        ; Op = ".",                 Info = op_info(infix(y, x), 10)
        ; Op = "..",                Info = op_info(infix(x, x), 550)
        ; Op = ":",                 Info = op_info(infix(y, x), 120)
        ; Op = "::",                Info = op_info(infix(x, x), 1175)
        ; Op = ":=",                Info = op_info(infix(x, x), 650)
        ; Op = "==>",               Info = op_info(infix(x, x), 1175)
        ; Op = "=^",                Info = op_info(infix(x, x), 650)
        ; Op = "@",                 Info = op_info(infix(x, x), 90)
        ; Op = "or_else",           Info = op_info(infix(x, y), 1100)
        ; Op = "end_module",        Info = op_info(prefix(x), 1199)
        ; Op = "event",             Info = op_info(prefix(x), 100)
        ; Op = "finalise",          Info = op_info(prefix(x), 1199)
        ; Op = "finalize",          Info = op_info(prefix(x), 1199)
        ; Op = "func",              Info = op_info(prefix(x), 800)
        ; Op = "import_module",     Info = op_info(prefix(x), 1199)
        ; Op = "impure",            Info = op_info(prefix(y), 800)
        ; Op = "include_module",    Info = op_info(prefix(x), 1199)
        ; Op = "initialise",        Info = op_info(prefix(x), 1199)
        ; Op = "initialize",        Info = op_info(prefix(x), 1199)
        ; Op = "inst",              Info = op_info(prefix(x), 1199)
        ; Op = "instance",          Info = op_info(prefix(x), 1199)
        ; Op = "mode",              Info = op_info(prefix(x), 1199)
        ; Op = "module",            Info = op_info(prefix(x), 1199)
        ; Op = "object",            Info = op_info(prefix(x), 1180)
        ; Op = "pragma",            Info = op_info(prefix(x), 1199)
        ; Op = "promise",           Info = op_info(prefix(x), 1199)
        ; Op = "semipure",          Info = op_info(prefix(y), 800)
        ; Op = "solver",            Info = op_info(prefix(y), 1181)
        ; Op = "type",              Info = op_info(prefix(x), 1180)
        ; Op = "typeclass",         Info = op_info(prefix(x), 1199)
        ; Op = "use_module",        Info = op_info(prefix(x), 1199)
        ),
        OtherInfos = []
    ;
        ( Op = "arbitrary"
        ; Op = "promise_equivalent_solutions"
        ; Op = "promise_equivalent_solution_sets"
        ; Op = "trace"
        ; Op = "atomic"
        ; Op = "try"
        ),
        Info = op_info(binary_prefix(x, y), 950),
        OtherInfos = []
    ;
        ( Op = "promise_exclusive"
        ; Op = "promise_exhaustive"
        ; Op = "promise_exclusive_exhaustive"
        ),
        Info = op_info(prefix(y), 950),
        OtherInfos = []
    ;
        ( Op = "promise_pure"
        ; Op = "promise_semipure"
        ; Op = "promise_impure"
        ),
        Info = op_info(prefix(x), 950),
        OtherInfos = []
    ).

%-----------------------------------------------------------------------------%

:- pragma inline(adjust_priority_for_assoc/3).

adjust_priority_for_assoc(Priority, y, Priority).
adjust_priority_for_assoc(Priority, x, Priority - 1).

%-----------------------------------------------------------------------------%
