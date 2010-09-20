%------------------------------------------------------------------------------%
% This file may only be copied under the terms of the GNU General
% Public License - see the file COPYING in the Venus distribution.
%------------------------------------------------------------------------------%
:- module error_util.

:- interface.

:- import_module prog_data.

:- import_module list.
:- import_module maybe.

:- type error_spec
    --->    error_spec(
                error_severity          :: error_severity,
                % error_phase             :: error_phase,
                error_msgs              :: list(error_msg)
            ).

:- type error_severity
    --->    severity_error
            % Always set the exit status to indicate an error.

    ;       severity_warning
            % Only set the exit status to indicate an error if --halt-at-warn
            % is enabled.

    ;       severity_informational
            % Don't set the exit status to indicate an error.

    /*
    ;       severity_conditional(
            % If the given boolean option has the given value, then the actual
            % severity is given by the third argument; if it has the other
            % value, then the actual severity is given by the fourth argument.
            % If the fourth argument is `no', then the error_spec shouldn't
            % actually print anything if cond_option doesn't have the value
            % in cond_option_value.

                cond_option             :: option,
                cond_option_value       :: bool,
                cond_if_match           :: error_severity,
                cond_if_no_match        :: maybe(error_severity)
            )
    */
    .

:- type actual_severity
    --->    actual_severity_error
    ;       actual_severity_warning
    ;       actual_severity_informational.

:- type error_msg
    --->    simple_msg(
                simple_context          :: prog_context,
                simple_components       :: list(error_msg_component)
            )
    ;       error_msg(
                error_context           :: maybe(prog_context),
                error_treat_as_first    :: maybe_treat_as_first,
                error_extra_indent      :: int,
                error_components        :: list(error_msg_component)
            ).

:- type maybe_treat_as_first
    --->    treat_as_first
    ;       do_not_treat_as_first.

:- type error_msg_component
    --->    always(format_components)
            % Print these components under all circumstances.

    /*
    ;       option_is_set(option, bool, list(error_msg_component))
            % Print the embedded components only if the specified boolean
            % option has the specified value.
    */

    ;       verbose_only(format_components)
            % Print these components only if --verbose-errors is specified.
            % If it is not specified, set the flag that triggers the printing
            % of the message reminding the user about --verbose-errors.

    ;       verbose_and_nonverbose(format_components, format_components)
            % If --verbose-errors is specified, print the first set of
            % components. If it is not specified, print the second set,
            % and set the flag that triggers the printing of the message
            % reminding the user about --verbose-errors.
    .

:- type format_component
    --->    fixed(string)   % This string should appear in the output
                            % in one piece, as it is.

    ;       quote(string)   % Surround the string with `' quotes, then treat
                            % as fixed.

    ;       int_fixed(int)  % Convert the integer to a string, then treat
                            % as fixed.

    ;       nth_fixed(int)  % Convert the integer to a string, such as
                            % "first", "second", "third", "4th", "5th" and
                            % then treat as fixed.
                            %

    ;       lower_case_next_if_not_first
                            % If this is the first component, ignore it.
                            % If this is not the first component, lower case
                            % the initial letter of the next component.
                            % There is no effect if the next component
                            % starts does not exist or does not start with
                            % an upper case letter.

    ;       prefix(string)  % This string should appear in the output
                            % in one piece, as it is, inserted directly
                            % before the next format_component, without
                            % any intervening space.

    ;       suffix(string)  % This string should appear in the output
                            % in one piece, as it is, appended directly
                            % after the previous format_component, without
                            % any intervening space.

    ;       words(string)   % This string contains words separated by
                            % white space. The words should appear in
                            % the output in the given order, but the
                            % white space may be rearranged and line
                            % breaks may be inserted.

    /*
    ;       sym_name(sym_name)
                            % The output should contain the string form of
                            % the sym_name, surrounded by `' quotes.

    ;       sym_name_and_arity(sym_name_and_arity)
                            % The output should contain the string form of
                            % the sym_name, followed by '/' and the arity,
                            % all surrounded by `' quotes.

    ;       top_ctor_of_type(mer_type)
                            % The top level type constructor of the given type,
                            % which must have one (i.e. must not be a
                            % variable).

    ;       p_or_f(pred_or_func)
                            % Output the string "predicate" or "function"
                            % as appropriate.

    ;       simple_call(simple_call_id)
                            % Output the identity of the given call.
    */ 

    ;       nl              % Insert a line break if there has been text
                            % output since the last line break.

    ;       nl_indent_delta(int)
                            % Act as nl, but also add the given integer
                            % (which should be a small positive or negative
                            % integer) to the current indent level.
    ;       blank_line.
                            % Create a blank line.

:- type format_components == list(format_component).

:- implementation.
