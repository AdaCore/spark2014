"""
This module contains support functions for the gnatprove testsuite

The functions in this module are expected to be imported either directly from
test.py scripts launched as standalone Python processes or from a dedicated
test driver which calls the functions in a Python instance that is shared
between multiple tests.

All printing to `stdout` must be done via calls to the `log` function defined
in this module. This function and all the top-level functions take an optional
parameter `logger` of type `e3.testsuite.result.Log`. This parameter must be
passed down through any calls that may require printing. Consequently, the
logging calls look like `log(logger, "some text")`.

The value of `logger` can be None in a call to the top-level function. The
effect is that all the messages and captured process outputs go to `stdout`.

Printing to `stderr` is not expected, but can be added in a similar fashion.
"""

import json
import os
import re
import subprocess
import sys

from e3.os.process import Run
from e3.testsuite.result import Log
from fnmatch import fnmatch
from time import sleep
from pathlib import Path
from shutil import copy, copytree, move, rmtree, which
import tempfile
from test_util import sort_key_for_errors

max_steps = 200
default_vc_timeout = 120
parallel_procs = 1
default_project = "test.gpr"
default_provers = ["cvc5", "altergo", "z3", "colibri"]
default_ada = 2022

#  Change directory

TEST = sys.modules["__main__"]
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

#  Format of message is the following:
#     file:line:column: qualifier: text extra_text
#  from which we extract:
#  - the file (group 1)
#  - the line (group 2)
#  - the qualifier (group 3)
#  - the text (group 5)
#
#  In particular, we separate out the extra_text which starts with a comma or
#  an opening parenthesis/bracket, that introduce additional information about
#  the part of a property that cannot be proved (", cannot prove bla"), that
#  give counterexample values ("(e.g. when bla)"), or that give an explanation
#  ("[possible explanation: bla]") as including these in the text of the
#  message can lead to bad identification of the message category when a
#  variable name coincides with some substrings that are searched in text.

is_msg = re.compile(
    r"([\w-]*\.ad.?):(\d*):\d*:" r" (info|warning|low|medium|high)?(: )?([^(,[]*)(.*)?$"
)
is_mark = re.compile(r"@(\w*):(\w*)")


# OutputRefiner Classes
# Classes for processing and refining lists of output strings
#
# Refiners can be validators (check output but don't modify) or transformers.
# Default refiners include: CheckMarks, CheckFail, CheckSarif, SparkLibFilter, Sort
#
# Usage Examples:
#   # Use default refiners (validate + filter SPARKlib + sort):
#   gnatprove(opt=["-P", "test.gpr"])
#
#   # Disable all refiners (no validation, filtering, or sorting):
#   gnatprove(opt=["-P", "test.gpr"], refiners=[])
#
#   # Keep defaults but disable sorting:
#   gnatprove(opt=["-P", "test.gpr"],
#             refiners=without_refiner(default_refiners(), SortRefiner))
#
#   # Keep defaults but disable mark checking:
#   gnatprove(opt=["-P", "test.gpr"],
#             refiners=without_refiner(default_refiners(), CheckMarksRefiner))
#
#   # Custom refiners (validate, filter by regex, then sort):
#   gnatprove(opt=["-P", "test.gpr"],
#             refiners=[CheckMarksRefiner(),
#                       RegexFilterRefiner("warning.*"),
#                       SortRefiner()])
class OutputRefiner:
    """Base class for output refiners that transform lists of strings.

    Refiners can either:
    1. Transform output (return modified list)
    2. Validate output (return original list, but may log errors/warnings)
    """

    def refine(self, lines: list[str]) -> list[str]:
        """Process a list of strings and return a list (potentially modified).

        Args:
            lines: List of strings to process

        Returns:
            Transformed or original list of strings
        """
        raise NotImplementedError("Subclasses must implement refine()")

    def set_context(self, cwd=None, logger=None, **kwargs):
        """Set context information needed by the refiner.

        Args:
            cwd: Working directory for file operations
            logger: Logger for output
            **kwargs: Additional context parameters specific to refiners
        """
        self.cwd = cwd
        self.logger = logger
        for key, value in kwargs.items():
            setattr(self, key, value)


class SortRefiner(OutputRefiner):
    """Sorts output lines by error sorting key."""

    def refine(self, lines: list[str]) -> list[str]:
        sorted_lines = lines.copy()
        sorted_lines.sort(key=sort_key_for_errors)
        return sorted_lines


class SparkLibFilterRefiner(OutputRefiner):
    """Filters out SPARKlib-related output lines."""

    sparklib_regex = re.compile(r"spark-.*\.ad[bs]:(\d*):\d*: info: .*")

    def refine(self, lines: list[str]) -> list[str]:
        return [line for line in lines if self.sparklib_regex.match(line) is None]


class RegexFilterRefiner(OutputRefiner):
    """Filters lines based on a regex pattern."""

    def __init__(self, pattern: str, invert: bool = True):
        """Initialize regex filter.

        Args:
            pattern: Regular expression pattern to match
            invert: If True, keep lines that DON'T match (default behavior)
        """
        self.pattern = pattern
        self.invert = invert

    def refine(self, lines: list[str]) -> list[str]:
        return grep(self.pattern, lines, invert=self.invert)


class CheckMarksRefiner(OutputRefiner):
    """Validates that marks in source code have matching results.

    This refiner doesn't modify output but performs validation checks.
    """

    def refine(self, lines: list[str]) -> list[str]:
        check_marks(lines, cwd=self.cwd, logger=self.logger)
        return lines


class CheckFailRefiner(OutputRefiner):
    """Validates that no unproved checks are in the output.

    This refiner doesn't modify output but performs validation checks.
    Always checks for failures - include it in refiners list only when needed.
    """

    def refine(self, lines: list[str]) -> list[str]:
        check_fail(lines, no_failures_allowed=True, logger=self.logger)
        return lines


class CheckSarifRefiner(OutputRefiner):
    """Validates SARIF output against tool output.

    It is checked that each SARIF message is included in the tool output.

    This refiner doesn't modify output but performs validation checks.
    Always checks SARIF - include it in refiners list only when needed.
    """

    def __init__(self, report: str | None = None):
        """Initialize SARIF checker.

        Args:
            report: Report type (corresponds to gnatprove --report switch)
        """
        self.report = report

    def refine(self, lines: list[str]) -> list[str]:
        check_sarif(lines, self.report, cwd=self.cwd, logger=self.logger)
        return lines


class GeneratedContractsRefiner(OutputRefiner):
    """Separates and sorts generated contract blocks and message lines.

    Message lines (file:line:col:...) are sorted separately using sort_key_for_errors.
    Generated contract blocks (starting with "Generated contracts for ...") are sorted
    alphabetically by entity name while preserving line order within each block.
    """

    def refine(self, lines: list[str]) -> list[str]:
        message_lines = []
        contract_blocks = []
        current_block = []
        other_lines = []

        for line in lines:
            # Check if it's a message line (file:line:col:...)
            if is_msg.match(line):
                message_lines.append(line)
            elif line.startswith("Generated contracts for "):
                # Start a new contract block
                if current_block:
                    contract_blocks.append(current_block)
                current_block = [line]
            elif current_block:
                # Add to current contract block
                current_block.append(line)
            else:
                # Line doesn't fit any pattern and we're not in a block
                other_lines.append(line)

        # Don't forget the last block
        if current_block:
            contract_blocks.append(current_block)

        # Sort message lines using the error sorting key
        message_lines.sort(key=sort_key_for_errors)

        # Sort contract blocks alphabetically by their first line (entity name)
        contract_blocks.sort(key=lambda block: block[0] if block else "")

        # Combine: contract blocks first, then message lines, then any other lines
        result = []
        for block in contract_blocks:
            result.extend(block)
        result.extend(message_lines)
        result.extend(other_lines)

        return result


# Helper functions and constants for common refiner configurations


def default_refiners(
    no_fail: bool = False, do_sarif_check: bool = False, report: str | None = None
) -> list[OutputRefiner]:
    """Return the default list of output refiners.

    Returns a fresh list containing the default refiners:
    [CheckMarksRefiner(), (CheckFailRefiner if no_fail), (CheckSarifRefiner if enabled),
     SparkLibFilterRefiner(), SortRefiner()]

    Args:
        no_fail: Whether to include CheckFailRefiner
        do_sarif_check: Whether to include CheckSarifRefiner
        report: Report type for SARIF checking

    Users can modify this list to customize behavior while keeping some defaults.
    """
    refiners = [CheckMarksRefiner()]

    if no_fail:
        refiners.append(CheckFailRefiner())

    if do_sarif_check:
        refiners.append(CheckSarifRefiner(report))

    refiners.extend([SparkLibFilterRefiner(), SortRefiner()])

    return refiners


def without_refiner(
    refiners: list[OutputRefiner], refiner_type: type
) -> list[OutputRefiner]:
    """Remove all refiners of a specific type from a list.

    Args:
        refiners: List of refiners to filter
        refiner_type: The class type to remove (e.g., SortRefiner)

    Returns:
        New list with refiners of the specified type removed

    Example:
        # Get defaults but without sorting:
        refiners = without_refiner(default_refiners(), SortRefiner)
    """
    return [r for r in refiners if not isinstance(r, refiner_type)]


def default_refiners_no_sort(
    no_fail: bool = False, do_sarif_check: bool = False, report: str | None = None
) -> list[OutputRefiner]:
    """Return the default list of output refiners without sorting."""
    refiners = default_refiners(no_fail, do_sarif_check, report)
    return without_refiner(refiners, SortRefiner)


def build_refiners_from_flags(
    no_fail: bool = False,
    filter_sparklib: bool = True,
    sort_output: bool = True,
    filter_output: str | None = None,
    do_sarif_check: bool = False,
    report: str | None = None,
) -> list[OutputRefiner]:
    """Build a list of refiners from boolean flags (for YAML compatibility).

    This helper is used by prove_all/do_flow to convert their boolean parameters
    into refiners for the gnatprove function.

    Args:
        no_fail: Whether to include CheckFailRefiner
        filter_sparklib: Whether to filter SPARKlib lines
        sort_output: Whether to sort output
        filter_output: Optional regex pattern to filter output
        do_sarif_check: Whether to include CheckSarifRefiner
        report: Report type for SARIF checking

    Returns:
        List of configured OutputRefiner instances
    """
    refiners = []

    # Validators - always include marks, conditionally include fail and SARIF
    refiners.append(CheckMarksRefiner())

    if no_fail:
        refiners.append(CheckFailRefiner())

    if do_sarif_check:
        refiners.append(CheckSarifRefiner(report))

    if filter_sparklib:
        refiners.append(SparkLibFilterRefiner())
    if filter_output is not None:
        refiners.append(RegexFilterRefiner(filter_output))

    if sort_output:
        refiners.append(SortRefiner())

    return refiners


def _base_path(cwd):
    return Path(cwd) if cwd else Path(".")


def _resolve_path(filename, cwd):
    p = Path(filename)
    if p.is_absolute():
        return p
    base = _base_path(cwd)
    return base / filename


def run_command(command, cwd=None, timeout=None):
    """
    Executes a command in a subprocess with a timeout.

    The process is executed via e3.process.Run which has platform-specific
    logic to reliably kill a process tree upon timeout. Calling Python's
    subprocess.run() is specifically avoided because it cannot kill process
    trees reliably on Windows.

    Args:
        command (list): The command to run.
        cwd (str, optional): Current working directory.
        timeout (int, optional): Timeout in seconds.

    Returns:
        An instance of e3.process.Run if the process completed before timeout.

    Raises:
        subprocess.TimeoutExpired: If the timeout is reached.
    """

    result = Run(
        command,
        cwd=cwd,
        timeout=timeout,
    )

    # e3.process.Run executes the command through a custom rlimit tool. On
    # timeout it returns with status 2 and a message like "rlimit: Real time
    # limit (<value> s) exceeded". We need to check both to know that it was
    # really a timeout.
    if (
        result.status == 2
        and result.out
        and result.out.strip().splitlines()[-1].startswith("rlimit:")
    ):
        raise subprocess.TimeoutExpired(cmd=command, timeout=timeout)

    return result


def benchmark_mode():
    if "benchmark" in os.environ:
        return os.environ["benchmark"]
    else:
        return None


def cache_mode():
    return "cache" in os.environ and os.environ["cache"] == "true"


def coverage_mode():
    return "coverage" in os.environ and os.environ["coverage"] == "true"


def cache_option():
    if "GNATPROVE_CACHE" in os.environ:
        cache = os.environ["GNATPROVE_CACHE"]
    else:
        cache = "localhost:11211"
    return f"--memcached-server={cache}"


def why3server_mode():
    if "why3server" in os.environ:
        return os.environ["why3server"]
    else:
        return None


def get_default_timeout():
    if "vc_timeout" in os.environ:
        return int(os.environ["vc_timeout"])
    else:
        return default_vc_timeout


def log(logger: Log | None, line: str) -> None:
    if logger:
        logger += f"{line}\n"
    else:
        print(line)


def log_sorted(logger: Log | None, lines: list[str]) -> None:
    lines.sort(key=sort_key_for_errors)
    for line in lines:
        log(logger, line)


def build_prover_switch(proverlist):
    """from a list of prover names, produce the option to be passed to
    gnatprove"""
    if len(proverlist) == 0:
        return []
    else:
        return ["--prover=" + ",".join(proverlist)]


def cat(filename, sort=False, start=1, end=0, cwd=None, logger=None):
    """Dump the content of a file on stdout

    PARAMETERS
      filename: name of the file to print on stdout
      start: first line to output, starting from line 1
      end: last line to output if not 0
      cwd: base directory to interpret relative filenames
    """
    path = _resolve_path(filename, cwd)
    if path.exists():
        with open(path, "r") as f:
            # Dump all the file
            if end == 0:
                if sort:
                    log_sorted(logger, f.readlines())
                else:
                    # read entire content; avoid duplicating trailing newlines
                    content = f.read()
                    log(logger, content.rstrip("\n"))
            # Dump only the part of the file between lines start and end
            else:
                lines = []
                for i, line in enumerate(f):
                    if i + 1 >= start and i + 1 <= end:
                        lines.append(line)
                if sort:
                    log_sorted(logger, lines)
                else:
                    for line in lines:
                        log(logger, line.rstrip("\n"))
    else:
        log(logger, f"Error: The path {path!r} does not exist.")


def ls(path=".", exclude_pattern=None, cwd=None, logger=None):
    base = _base_path(cwd)
    target = base / path if not Path(path).is_absolute() else Path(path)
    try:
        if target.is_file():
            log(logger, str(target))
        elif target.is_dir():
            entries = os.listdir(target)
            entries.sort()

            if exclude_pattern:
                entries = [
                    entry for entry in entries if not fnmatch(entry, exclude_pattern)
                ]

            for entry in entries:
                log(logger, entry)
        else:
            log(logger, f"Error: '{str(target)!r}' is neither a file nor a directory.")
    except FileNotFoundError:
        log(logger, f"Error: The path '{str(target)!r}' does not exist.")
    except PermissionError:
        log(logger, f"Error: Permission denied to access '{str(target)!r}'.")


def matches(comp_reg, s, invert):
    """decide whether string s matches the compiled regex comp_reg

    PARAMETERS
    comp_reg: a compiled regex
    s: a string to be matched
    invert: if false, negate the result
    """
    m = re.match(comp_reg, s)
    return (invert and not m) or (not invert and m)


def verify_counterexamples(cwd=None, logger=None):
    """Checks that marks in source code have a matching counterexample.

    Marks are strings in the source that have the format
        @COUNTEREXAMPLE
    For each such mark, either issue an error if there is no corresponding
    counterexample, or display the counterexample trace in a human readable
    form in the output.

    """
    base = _base_path(cwd)
    files = sorted([p.name for p in base.glob("*.ad?")])
    result_files = list(base.glob("gnatprove/*.spark"))
    is_mark_local = re.compile(r"@COUNTEREXAMPLE")

    def not_found(f, line):
        """Log an error that the requested mark has not been found"""
        log(logger, "MISSING COUNTEREXAMPLE at " + f + ":" + str(line))

    # store actual results in a map from (file,line) to a list of strings
    # for the counterexample, where each element of the list gives the
    # pairs (name,value) for the counterexample in a different line of
    # code.
    results = {}

    have_populated_dict = False

    def compute_results_dict():
        nonlocal results, have_populated_dict
        if have_populated_dict:
            return
        have_populated_dict = True
        for result_file in result_files:
            try:
                with open(result_file, "r") as f:
                    result = json.load(f)
            except FileNotFoundError:
                continue
            proof_result = result.get("proof", [])
            for msg in proof_result:
                msg_file = msg.get("file")
                msg_line = msg.get("line")

                # list of strings for the trace attached to the counterexample.
                # In fact we store here pairs of a location (file,line) and
                # a string for the trace element, so that we can sort the trace
                # based on location before displaying it.
                msg_list = []

                def str_elem(val):
                    return str(val["name"]) + " = " + str(val["value"])

                def location(arg):
                    return arg[0]

                def trace(arg):
                    return arg[1]

                if "cntexmp" in msg:
                    for ff, file_value in msg["cntexmp"].items():
                        if "current" in file_value:
                            for line, values in file_value["current"].items():
                                ctx = f"  trace at {ff}:{line} --> " + " and ".join(
                                    map(str_elem, values)
                                )
                                msg_list.append(((ff, int(line)), ctx))
                        if "previous" in file_value:
                            for line, values in file_value["previous"].items():
                                ctx = (
                                    f"[PREVIOUS]  trace at {ff}:{line} --> "
                                    + " and ".join(map(str_elem, values))
                                )
                                msg_list.append(((ff, int(line)), ctx))

                    # sort the trace elements based on location
                    msg_list.sort(key=location)

                    # store only the list of trace elements, not locations.
                    # Note that only the last counterexample for a given
                    # location (msg_file,msg_line) is stored in results, when
                    # multiple counterexamples are present on the same line.
                    results[(msg_file, msg_line)] = [trace(item) for item in msg_list]

    # check that marks in source code have a matching counterexample, and
    # display the counterexample when found.
    for f in files:
        path_to_open = _resolve_path(f, cwd)
        try:
            with open(path_to_open, "r", encoding="iso-8859-1") as ff:
                for line_no, linestr in enumerate(ff):
                    lineno = line_no + 1  # first line in file is 1, not 0
                    for _mark in re.finditer(is_mark_local, linestr):
                        compute_results_dict()
                        key = (f, lineno)
                        if key in results:
                            log(
                                logger,
                                f"counterexample expected for check at {f}:{lineno}",
                            )
                            for ctx in results[key]:
                                log(logger, ctx)
                        else:
                            not_found(f, lineno)
        except FileNotFoundError:
            # If the file cannot be read, log and continue
            log(logger, f"Error: file not found {path_to_open!s}")


def check_fail(strlist, no_failures_allowed, logger=None):
    """Makes sure that we did not have any failed proof attempts."""

    failures = frozenset(["low", "medium", "high"])

    if no_failures_allowed:
        for m in map(is_msg.match, strlist):
            if m is not None:
                kind = m.group(3)
                if kind in failures:
                    log(
                        logger,
                        "FAILED CHECK UNEXPECTED at %s:%s" % (m.group(1), m.group(2)),
                    )


def is_dependency_tag(tag):
    """Returns True if the given tag corresponds to a dependency flow
    message"""
    return tag in ("DEPENDS", "GLOBAL")


def is_flow_initialization_tag(tag):
    """Returns True if the given tag corresponds to an initialization flow
    message"""
    return tag in ("INITIALIZED", "INITIALIZES")


def is_termination_tag(tag):
    return tag in ("TERMINATION")


def is_aliasing_tag(tag):
    """Returns True if the given tag corresponds to an aliasing flow message"""
    return tag in ("ALIASING")


def is_other_flow_tag(tag):
    """Returns True if the given tag corresponds to another flow message"""
    return tag in ("BOUNDARY_CALL_IN_INVARIANT")


def is_rte_tag(tag):
    """Returns True if the given tag corresponds to a RTE proof message"""
    return tag in (
        "DIVISION_CHECK",
        "FLOAT_OVERFLOW_CHECK",
        "INDEX_CHECK",
        "OVERFLOW_CHECK",
        "RANGE_CHECK",
        "LENGTH_CHECK",
        "DISCRIMINANT_CHECK",
        "TAG_CHECK",
        "NULL_EXCLUSION",
        "ACCESSIBILITY_CHECK",
        "RESOURCE_LEAK",
        "RESOURCE_LEAK_AT_END_OF_SCOPE",
        "DEREFERENCE_CHECK",
        "UU_RESTRICTION",
        "CEILING_INTERRUPT",
        "CEILING_PRIORITY_PROTOCOL",
        "INTERRUPT_RESERVED",
        "TASK_TERMINATION",
        "VALIDITY_CHECK",
    )


def is_proof_initialization_tag(tag):
    """Returns True if the given tag corresponds to an initialization proof
    message"""
    return tag in ("INIT_BY_PROOF")


def is_ada_assertion_tag(tag):
    """Returns True if the given tag corresponds to an Ada assertion proof
    message"""
    return tag in (
        "PREDICATE_CHECK",
        "PREDICATE_CHECK_ON_DEFAULT_VALUE",
        "INVARIANT_CHECK",
        "INVARIANT_CHECK_ON_DEFAULT_VALUE",
        "PRECONDITION",
        "PRECONDITION_MAIN",
        "POSTCONDITION",
        "ASSERT",
    )


def is_spark_assertion_tag(tag):
    """Returns True if the given tag corresponds to a SPARK assertion proof
    message"""
    return tag in (
        "DEFAULT_INITIAL_CONDITION",
        "CONTRACT_CASE",
        "DISJOINT_CASES",
        "COMPLETE_CASES",
        "LOOP_INVARIANT_INIT",
        "LOOP_INVARIANT_PRESERV",
        "LOOP_INVARIANT",
        "LOOP_VARIANT",
        "REFINED_POST",
        "SUBPROGRAM_VARIANT",
        "EXCEPTIONAL_CASE",
        "PROGRAM_EXIT_POST",
        "EXIT_CASE",
    )


def is_other_proof_tag(tag):
    """Returns True if the given tag corresponds to another proof message"""
    return tag in (
        "INITIAL_CONDITION",
        "RAISE",
        "UNEXPECTED_PROGRAM_EXIT",
        "TRIVIAL_PRE",
        "WEAKER_PRE",
        "STRONGER_POST",
        "WEAKER_CLASSWIDE_PRE",
        "STRONGER_CLASSWIDE_POST",
        "WEAKER_PRE_ACCESS",
        "STRONGER_POST_ACCESS",
        "UNCHECKED_CONVERSION",
        "UNCHECKED_CONVERSION_SIZE",
        "UNCHECKED_CONVERSION_ALIGN",
        "UNCHECKED_CONVERSION_VOLATILE",
        "ASSERT_PREMISE",
        "ASSERT_STEP",
        "INLINE_ANNOTATION",
        "CONTAINER_AGGR_ANNOTATION",
        "RECLAMATION_ENTITY",
        "FEASIBLE_POST",
    )


def is_flow_tag(tag):
    """Returns True if the given tag corresponds to a flow message"""
    return (
        is_dependency_tag(tag)
        or is_flow_initialization_tag(tag)
        or is_aliasing_tag(tag)
        or is_other_flow_tag(tag)
    )


def is_proof_tag(tag):
    """Returns True if the given tag corresponds to a proof message"""
    return (
        is_rte_tag(tag)
        or is_proof_initialization_tag(tag)
        or is_ada_assertion_tag(tag)
        or is_spark_assertion_tag(tag)
        or is_termination_tag(tag)
        or is_other_proof_tag(tag)
    )


def check_marks(strlist, cwd=None, logger=None):
    """Checks that marks in source code have a matching result.

    Given the output from flow analysis and/or proof, check that all marks
    mentioned in source files have a matching expected result, where source
    files are taken to be the *.ad? files in the specified cwd (or current
    directory if None).

    Marks are any strings in the source that have the format
        @TAG:RESULT
    where both TAG and RESULT are alphanumeric strings without space, possibly
    with underscores. A tag denotes a line where some result is expected
    (typically this marker will be put in comments).

    TAG is either:
    - a check (RANGE_CHECK, DIVISION_CHECK, etc), or
    - a flow message (UNINIT, DEPENDS, etc).

    The complete list of tags is given by functions is_flow_tag and
    is_proof_tag.

    RESULT is either
    - PASS/FAIL for checks, or
    - ERROR/CHECK/WARN for flow messages, or
    - NONE for no such check/message.

    Case does not matter for the tag or result, although UPPERCASE is better in
    source code to easily locate the marks visually.

    """
    base = _base_path(cwd)
    files = [p.name for p in base.glob("*.ad?")]

    def get_tag(text):
        """Returns the tag for a given message text, or None if no tag is
        recognized."""

        # ??? simple string matching doesn't quite work when the message
        # contains several tags at once (e.g. 'global "xxx" is aliased')
        # or when the tag appears in an object name
        # (e.g. '"aliased" is missing from the Global contract')

        # flow analysis tags

        # When adding a tag in this section, you need also to update the
        # function is_flow_tag below.
        if "aliased" in text and "aliased objects" not in text:
            return "ALIASING"
        elif "dependency" in text:
            return "DEPENDS"
        elif "global" in text:
            return "GLOBAL"
        elif "initialized" in text or "set" in text:
            return "INITIALIZED"
        elif "initializes" in text:
            return "INITIALIZES"
        elif "call boundary subprogram" in text:
            return "BOUNDARY_CALL_IN_INVARIANT"

        # proof tags

        # When adding a tag in this section, you need also to update the
        # function is_proof_tag below.
        elif "aspect Always_Terminates" in text or (
            (
                "not terminate" in text
                or "termination" in text
                or "nonterminating" in text
            )
            and ("call" in text or "loop" in text)
        ):
            return "TERMINATION"
        elif "division check" in text or "divide by zero" in text:
            return "DIVISION_CHECK"
        elif "index check" in text:
            return "INDEX_CHECK"
        elif "float overflow check" in text:
            return "FLOAT_OVERFLOW_CHECK"
        elif "overflow check" in text:
            return "OVERFLOW_CHECK"
        elif "predicate check" in text:
            if "on default value" in text:
                return "PREDICATE_CHECK_ON_DEFAULT_VALUE"
            else:
                return "PREDICATE_CHECK"
        elif "invariant check" in text:
            if "on default value" in text:
                return "INVARIANT_CHECK_ON_DEFAULT_VALUE"
            else:
                return "INVARIANT_CHECK"
        elif "range check" in text:
            return "RANGE_CHECK"
        elif "length check" in text:
            return "LENGTH_CHECK"
        elif "discriminant check" in text:
            return "DISCRIMINANT_CHECK"
        elif "tag check" in text:
            return "TAG_CHECK"
        elif "initialization check" in text:
            return "INIT_BY_PROOF"
        elif "null exclusion check" in text:
            return "NULL_EXCLUSION"
        elif "accessibility check" in text:
            return "ACCESSIBILITY_CHECK"
        elif "resource or memory leak" in text:
            if "at end of scope" in text:
                return "RESOURCE_LEAK_AT_END_OF_SCOPE"
            else:
                return "RESOURCE_LEAK"
        elif "dereference check" in text:
            return "DEREFERENCE_CHECK"
        elif "validity check" in text:
            return "VALIDITY_CHECK"
        elif "operation on unchecked union type" in text:
            return "UU_RESTRICTION"
        elif "ceiling priority" in text:
            if "in Interrupt_Priority" in text:
                return "CEILING_INTERRUPT"
            else:
                return "CEILING_PRIORITY_PROTOCOL"
        elif "interrupt" in text and ("reserved" in text or "availability" in text):
            return "INTERRUPT_RESERVED"
        elif "default initial condition" in text:
            return "DEFAULT_INITIAL_CONDITION"
        elif "task" in text and ("nontermination" in text or "terminate" in text):
            return "TASK_TERMINATION"
        elif "initial condition" in text:
            return "INITIAL_CONDITION"
        elif "precondition" in text:
            if "of main program" in text:
                return "PRECONDITION_MAIN"
            elif "True" in text:
                return "TRIVIAL_PRE"
            elif "class-wide" in text and "overridden" in text:
                return "WEAKER_CLASSWIDE_PRE"
            elif "class-wide" in text:
                return "WEAKER_PRE"
            elif "target" in text:
                return "WEAKER_PRE_ACCESS"
            else:
                return "PRECONDITION"
        elif "refined post" in text:
            return "REFINED_POST"
        elif "program exit postcondition" in text:
            return "PROGRAM_EXIT_POST"
        elif "exit the program" in text:
            return "UNEXPECTED_PROGRAM_EXIT"
        elif "postcondition" in text:
            if "class-wide" in text and "overridden" in text:
                return "STRONGER_CLASSWIDE_POST"
            elif "class-wide" in text:
                return "STRONGER_POST"
            elif "target" in text:
                return "STRONGER_POST_ACCESS"
            else:
                return "POSTCONDITION"
        elif "disjoint" in text and "cases" in text:
            return "DISJOINT_CASES"
        elif "complete" in text and "cases" in text:
            return "COMPLETE_CASES"
        elif "contract case" in text:
            return "CONTRACT_CASE"
        elif "exit case" in text:
            return "EXIT_CASE"
        elif "loop invariant" in text:
            if "initialization" in text or "in first iteration" in text:
                return "LOOP_INVARIANT_INIT"
            elif "preservation" in text or "by an arbitrary iteration" in text:
                return "LOOP_INVARIANT_PRESERV"
            else:
                return "LOOP_INVARIANT"
        elif "loop variant" in text:
            return "LOOP_VARIANT"
        elif "subprogram variant" in text:
            return "SUBPROGRAM_VARIANT"
        elif "assertion premise" in text:
            return "ASSERT_PREMISE"
        elif "assertion step" in text:
            return "ASSERT_STEP"
        elif "assertion" in text:
            return "ASSERT"
        elif "raise statement" in text or "expected exception" in text:
            return "RAISE"
        elif (
            "aliasing via address clause" in text
            or "aliased objects" in text
            or "unchecked conversion" in text
        ):
            if "size" in text:
                return "UNCHECKED_CONVERSION_SIZE"
            else:
                return "UNCHECKED_CONVERSION"
        elif "alignment" in text:
            return "UNCHECKED_CONVERSION_ALIGN"
        elif "object with non-trivial address clause" in text:
            return "UNCHECKED_CONVERSION_VOLATILE"
        elif "Inline_For_Proof or Logical_Equal annotation" in text:
            return "INLINE_ANNOTATION"
        elif "Container_Aggregates annotation" in text:
            return "CONTAINER_AGGR_ANNOTATION"
        elif "reclamation entity" in text:
            return "RECLAMATION_ENTITY"
        elif "feasible" in text or "feasibility" in text:
            return "FEASIBLE_POST"
        elif "exceptional case" in text:
            return "EXCEPTIONAL_CASE"

        # no tag recognized
        return None

    def is_negative_result(result):
        """Returns True if the given result corresponds to a negative one"""
        return result != "PASS"

    def is_valid_result(result):
        """Returns True if the given result corresponds to a valid one"""
        return result in ("PASS", "FAIL", "CHECK", "WARN", "ERROR", "NONE")

    def get_result(qualifier, text, is_flow_tag):
        """Returns the result for a given message qualifier and text.

        PARAMETERS
          qualifier:   either 'info' or 'warning'
          text:        text of the message, stripped of the initial qualifier
          is_flow_tag: True for flow messages, False for proof messages
        """
        if qualifier == "info":
            if (
                "proved" in text
                or "only expected" in text
                or "justified"
                or "respected" in text
            ):
                return "PASS"
            else:
                return None
        elif qualifier == "warning":
            if is_flow_tag:
                return "WARN"
            else:
                return "FAIL"
        elif qualifier == "low" or qualifier == "medium" or qualifier == "high":
            if is_flow_tag:
                return "CHECK"
            else:
                return "FAIL"
        else:
            return "ERROR"

    def not_found(f, line, tag, result):
        """Print an error that the requested mark has not been found"""
        if is_negative_result(result):
            prefix = "SOUNDNESS BUG "
        else:
            assert is_proof_tag(tag)
            prefix = "PROOF REGRESSION "
        log(logger, prefix + f"at {f}:{line}: mark @{tag}:{result} not found")

    def bad_found(f, line, tag, result):
        """Print an error that the mark has been unexpectedly found"""
        log(logger, f"SPURIOUS MESSAGE at {f}:{line}: message @{tag}:{result} found")

    # store actual results in a map from (file,line) to (TAG,RESULT)
    results = {}

    for msg in strlist:
        m = re.match(is_msg, msg)
        if m:
            f = m.group(1)
            line = int(m.group(2))
            qual = m.group(3)
            text = m.group(5)
            tag = get_tag(text)
            if tag:
                res = get_result(qual, text, is_flow_tag(tag))
                results.setdefault((f, line), set()).add((tag, res))

    # check that marks in source code have a matching actual result
    for f in files:
        path_to_open = _resolve_path(f, cwd)
        try:
            with open(path_to_open, "r", encoding="iso-8859-1") as ff:
                for line_no, linestr in enumerate(ff):
                    lineno = line_no + 1  # first line in file is 1, not 0
                    for mark in re.finditer(is_mark, linestr):
                        tag = mark.group(1).upper()

                        if not (is_flow_tag(tag) or is_proof_tag(tag)):
                            log(logger, f"unrecognized tag {tag} at {f}:{lineno}")
                            sys.exit(1)
                        res = mark.group(2).upper()

                        if not is_valid_result(res):
                            log(logger, "unrecognized result {res} at {f}:{line}")
                            sys.exit(1)

                        if res == "NONE":
                            if (f, lineno) in results:
                                for tag2, res2 in results[f, lineno]:
                                    if tag == tag2:
                                        bad_found(f, lineno, tag2, res2)
                        else:
                            if (f, lineno) not in results or (tag, res) not in results[
                                f, lineno
                            ]:
                                not_found(f, lineno, tag, res)
        except FileNotFoundError:
            log(logger, f"Error: file not found {path_to_open!s}")


def gcc(src, opt=None, cwd=None, logger=None):
    """gcc wrapper for the testsuite

    PARAMETERS
       src: source file to process
       opt: additional options to pass to gcc
       cwd: base directory for relative paths
    """
    if opt is None:
        opt = ["-c"]
    cmd = ["gcc"]
    cmd += to_list(opt)
    cmd += [src]
    process = run_command(cmd, cwd=cwd)
    log_sorted(logger, str.splitlines(process.out))


def gprbuild(opt=None, sort_lines=True, cwd=None, logger=None):
    """Call gprbuld -q **opt. Sort the output if sort_lines is True."""
    if opt is None:
        opt = []
    process = run_command(["gprbuild", "-q"] + opt, cwd=cwd)
    lines = str.splitlines(process.out)
    if len(lines) == 0:
        return

    # Recognize the error markers for gprbuild 1 and gprbuild 2
    # and replace them with single message.
    error_found = False
    if " phase failed" in lines[-1] or " failed with status" in lines[-1]:
        error_found = True
        lines = lines[:-1]

    if sort_lines:
        log_sorted(logger, lines)
    else:
        for line in lines:
            log(logger, line)
    if error_found:
        log(logger, "[the gprbuild command failed]")


def spark_install_path():
    """the location of the SPARK install"""
    exec_loc = which("gnatprove")
    return os.path.dirname(os.path.dirname(exec_loc))


def preprocess_sparklib_source_file(filepath, logger=None):
    """
    Reads a file line by line and replaces specific SPARK_Mode patterns
    in-place, preserving line numbers.

    Args:
        filepath (str): The path to the file to be processed.
    """
    # Pattern 1: Recognizes '... SPARK_Mode => Off --  #BODYMODE' at the end of a line.
    # It's case-insensitive and handles variable whitespace.
    # This will be used with re.sub to replace 'Off' with 'On' while preserving
    # any leading content on the line.
    pattern_to_enable = re.compile(
        r"(SPARK_Mode\s*=>\s*)Off(\s*--  #BODYMODE\s*$)", re.IGNORECASE
    )

    # Pattern 2: Recognizes a line containing only
    # 'pragma SPARK_Mode (Off); -- # #BODYMODE'
    # It's case-insensitive and handles variable whitespace.
    pattern_to_remove = re.compile(
        r"^\s*pragma\s+SPARK_Mode\s*\(\s*Off\s*\)\s*;\s*--  #BODYMODE\s*$",
        re.IGNORECASE,
    )

    fd, temp_path = tempfile.mkstemp()

    try:
        with os.fdopen(fd, "w", newline="") as newfile:
            with open(filepath, "r", newline="") as oldfile:
                for line in oldfile:
                    # Test for the first pattern and replace using re.subn.
                    # re.subn returns a tuple: (new_string, number_of_subs_made).
                    # This handles cases where the pattern is not at the start
                    # of the line.
                    new_line, count = pattern_to_enable.subn(r"\1On\2", line)
                    if count > 0:
                        # If a substitution was made, write the modified line.
                        # new_line already contains the original newline
                        # character.
                        newfile.write(new_line)
                        continue

                    # Test for the second pattern.
                    # This pattern is expected to match the entire line.
                    match_remove = pattern_to_remove.match(line)
                    if match_remove:
                        if line.endswith("\r\n"):
                            # Preserve Windows-style line endings.
                            newfile.write("\r\n")
                        elif line.endswith("\n"):
                            # Preserve Unix-style line endings.
                            newfile.write("\n")
                        else:
                            # EOF case
                            pass
                        continue

                    # If no pattern is matched, write the original line back to
                    # the file.  'line' already contains a newline character.
                    newfile.write(line)

        # Replace the original file with the modified temporary file.
        move(temp_path, filepath)

    except FileNotFoundError:
        log(logger, f"Error: The file {filepath!r} was not found.")
        sys.exit(1)
    except Exception as e:
        log(logger, f"An unexpected error occurred: {e}")
        sys.exit(1)


def update_projectpath_for_sparklib(newpath):
    """check the paths in GPR_PROJECT_PATH; replace the one that contains
    sparklib by the path in argument."""
    gpp = os.environ["GPR_PROJECT_PATH"].split(os.pathsep)
    gpp = [
        path
        for path in gpp
        if not os.path.isfile(os.path.join(path, "sparklib_internal.gpr"))
    ]
    os.environ["GPR_PROJECT_PATH"] = os.pathsep.join([newpath] + gpp)


def create_sparklib(sparklib_bodymode=False, cwd=None, logger=None):
    """If sparklib_bodymode is false, simply create a sparklib.gpr.
    If sparklib_bodymode is true, in addition, create a copy of sparklib,
    with the following changes:
      - some SPARK_Mode => Off are replaced,
      - spark__exec.ads replaces spark.ads in both full and light runtime
    then change GPR_PROJECT_PATH to point to this new sparklib.

    The created files and directories are placed in `cwd` if provided,
    otherwise in the current working directory.
    """
    base_path = _base_path(cwd)
    project_file = base_path / "sparklib.gpr"
    # Ensure parent directory exists (usually base_path itself)
    base_path.mkdir(parents=True, exist_ok=True)

    with open(project_file, "w") as f_prj:
        f_prj.write('project SPARKlib extends "sparklib_internal" is\n')
        f_prj.write('   for Object_Dir use "sparklib_obj";\n')
        f_prj.write("   for Source_Dirs use SPARKlib_Internal'Source_Dirs;\n")
        f_prj.write(
            "   for Excluded_Source_Files use "
            + "SPARKlib_Internal'Excluded_Source_Files;\n"
        )
        f_prj.write("end SPARKlib;\n")
    if sparklib_bodymode:
        # goal is to create the following folders under base_path:
        # lib/gnat - contains project files
        # include/spark - contains src
        # then preprocess the src
        sparkinstall = spark_install_path()
        for rel in ["lib", "include"]:
            target_dir = base_path / rel
            if target_dir.is_dir():
                rmtree(str(target_dir))
        # copy install tree into base_path/lib and base_path/include
        copytree(os.path.join(sparkinstall, "lib"), str(base_path / "lib"))
        copytree(os.path.join(sparkinstall, "include"), str(base_path / "include"))
        src_prefix = base_path / "include" / "spark"
        for target in [
            src_prefix / "full" / "spark.ads",
            src_prefix / "light" / "spark.ads",
        ]:
            copy(str(src_prefix / "spark__exec.ads"), str(target))
        for path_obj in (base_path / "include").rglob("*"):
            if path_obj.is_file():
                preprocess_sparklib_source_file(str(path_obj), logger=logger)
        newpath = str((base_path / "lib" / "gnat").resolve())
        update_projectpath_for_sparklib(newpath)


def generate_project_file(ada=default_ada, sparklib=False, cwd=None):
    """
    Creates a GNAT project file and 'test.adc' configuration in the specified
    'cwd' (or current directory if None), provided the project file does not
    already exist.
    """

    base_path = _base_path(cwd)
    project_path = base_path / default_project
    adc_path = base_path / "test.adc"

    if not project_path.exists():
        with open(project_path, "w") as f_prj:
            if sparklib:
                f_prj.write('with "sparklib";\n')
            f_prj.write("project Test is\n")
            f_prj.write("  package Compiler is\n")
            f_prj.write(
                '    for Default_Switches ("Ada")'
                # discard warning messages by default
                + ' use ("-gnatws",'
                # force generation of BUGBOX even when error is issued
                + ' "-gnatdk", '
                + ' "-gnatd.k", '
                + '"-gnat'
                + str(ada)
                + '");\n'
            )
            f_prj.write('    for Local_Configuration_Pragmas use "test.adc";\n')
            f_prj.write("  end Compiler;\n")
            f_prj.write("end Test;\n")

        with open(adc_path, "w") as f_adc:
            f_adc.write("pragma SPARK_Mode (On);\n")
            f_adc.write("pragma Profile (Ravenscar);\n")
            f_adc.write("pragma Partition_Elaboration_Policy (Sequential);\n")


def gnatprove(
    opt=None,
    no_output=False,
    cache_allowed=True,
    exit_status=None,
    ada=default_ada,
    sparklib=False,
    info=True,
    report=None,
    sparklib_bodymode=False,
    refiners=None,
    cwd=None,
    timeout=None,
    logger=None,
):
    """Invoke gnatprove, and in case of success return list of output lines

    PARAMETERS
    opt: options to give to gnatprove
    no_output: do not display gnatprove output, only of interest for testing
               exit status
    exit_status: if set, expected value of the exit status from gnatprove
    refiners: list of OutputRefiner instances to process output. If None,
              uses default refiners:
                [CheckMarksRefiner(), SparkLibFilterRefiner(), SortRefiner()].
              Pass [] disable all refinement.
              To include validation, add CheckFailRefiner() or CheckSarifRefiner() to
              the list.
              See usage examples at top of file.

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """
    if opt is None:
        opt = ["-P", default_project]

    if report is not None:
        opt = [f"--report={report}"] + opt
    generate_project_file(ada, sparklib, cwd)

    # Generate sparklib.gpr if the project depends on SPARKlib
    if sparklib:
        create_sparklib(sparklib_bodymode=sparklib_bodymode, cwd=cwd, logger=logger)

    cmd = ["gnatprove"]
    # Continue on errors, to get the maximum number of messages for tests
    cmd += ["-k"]
    # Issue all information messages for tests
    if info:
        cmd += ["--info"]
    # If the tests uses SPARKlib, do not prove them again
    if sparklib:
        cmd += ["--no-subprojects"]
    if cache_allowed and cache_mode():
        cmd += [cache_option()]
    cmd += to_list(opt)
    # Add benchmark switches last to override existing ones
    if benchmark_mode() is not None:
        cmd += [
            "--benchmark",
            "--debug-save-vcs",
            "--proof-warnings=off",
            "--why3-debug",
            "gnat_ast",
        ]
    # When not interested in output, force --output=brief to get simpler diffs
    if no_output:
        cmd += ["--output=brief"]
    process = run_command(cmd, cwd=cwd, timeout=timeout)
    # Replace line above by the one below for testing the scripts without
    # running the tool:
    # process = open("test.out", 'r').read()

    # Check marks in source code and print the command output sorted
    strlist = str.splitlines(process.out)
    # Replace line above by the one below for testing the scripts without
    # running the tool
    # strlist = str.splitlines(process)

    # Check that the exit status is as expected
    if exit_status is not None and process.status != exit_status:
        log(logger, f"Unexpected exit status of {process.status}")
        failure = True
    else:
        failure = False

    # Apply refiners to output (includes validation and transformation)
    if refiners is None:
        refiners = [CheckMarksRefiner(), SparkLibFilterRefiner(), SortRefiner()]

    # Set context for all refiners
    for refiner in refiners:
        refiner.set_context(cwd=cwd, logger=logger, report=report)

    # Execute refiners in sequence
    for refiner in refiners:
        strlist = refiner.refine(strlist)

    if not no_output or failure:
        for line in strlist:
            log(logger, line)


def sarif_msg_text(result):
    msg = result["message"]
    fulltext = msg["text"]
    if "arguments" in msg:
        for index, value in enumerate(msg["arguments"]):
            placeholder = f"{{{index}}}"
            newvalue = (
                value
                if value.startswith('"') and value.endswith('"')
                else f'"{value}"'  # noqa: B907
            )
            fulltext = fulltext.replace(placeholder, newvalue)
    if "relatedLocations" in result:
        loc_map = {str(loc["id"]): loc for loc in result["relatedLocations"]}

    pattern = r"\[([^\]]+)\]\((\d+)\)"

    def loc_text(loc):
        return f'at line {loc["physicalLocation"]["region"]["startLine"]}'

    def _replacer(match: re.Match) -> str:
        original_link = match.group(0)
        item_id = match.group(2)
        loc = loc_map.get(item_id)

        if loc:
            return loc_text(loc)
        else:
            return original_link

    return re.sub(pattern, _replacer, fulltext)


ignore_patterns = [
    # TODO SPARK violation messages appear differently in SARIF, need to investigate
    "not allowed in SPARK",
    "not yet supported",
    # TODO these two messages is often issued for units other than the main
    # unit and doesn't appear because of that
    "function Is_Valid is assumed to return True",
    'attribute "Valid" is assumed to return True',
    # TODO we currently have trouble rendering the "at line ..." part of
    # unrolling messages:
    "cannot unroll loop",
]


def has_ignore_pattern(msg):
    for pattern in ignore_patterns:
        if pattern in msg:
            return True


def check_sarif(lines, report, cwd=None, logger=None):
    base = _base_path(cwd)
    potential_sarif_files = list(base.glob("**/gnatprove.sarif"))
    if len(potential_sarif_files) == 0:
        return
    sarif_file = potential_sarif_files[0]
    with open(sarif_file, "r") as f:
        sarif = json.load(f)

    def contains(text):
        for line in lines:
            if text in line:
                return True
        return False

    for result in sarif["runs"][0]["results"]:
        # ignore if result suppressed
        if "suppressions" in result and len(result["suppressions"]) > 0:
            continue
        # if in "report=fail" mode, ignore "proved" messages
        if report == "fail" and result["kind"] == "pass":
            continue
        msg = sarif_msg_text(result)
        if has_ignore_pattern(msg):
            continue

        if not contains(msg):
            log(
                logger,
                "the following SARIF message text is not part of the tool output:",
            )
            log(logger, msg)


def prove_all(
    opt=None,
    steps=None,
    procs=parallel_procs,
    vc_timeout=None,
    memlimit=2000,
    mode="all",
    counterexample=True,
    check_counterexamples=True,
    prover=default_provers,
    cache_allowed=True,
    report=None,
    project=default_project,
    level=None,
    no_fail=False,
    no_output=False,
    sort_output=True,
    filter_output=None,
    filter_sparklib=True,
    refiners=None,
    codepeer=False,
    exit_status=None,
    ada=default_ada,
    replay=False,
    warnings="continue",
    sparklib=False,
    enable_sarif_check=False,
    sparklib_bodymode=False,
    cwd=None,
    timeout=None,
    logger=None,
):
    """Call gnatprove with standard options.

    For option steps the default is max_steps set above, setting this
    option to zero disables steps option.

    Boolean parameters (sort_output, filter_output, filter_sparklib, no_fail and
    enable_sarif_check) are provided for YAML compatibility. They are converted to
    refiners internally.

    Advanced users can pass a custom refiners list to override all boolean flags.
    When refiners is not None, all boolean flags are ignored.

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """
    fullopt = ["--output=oneline"]
    if warnings is not None:
        fullopt += ["--warnings=%s" % (warnings)]
    fullopt += ["--assumptions"]
    fullopt += ["-P", project, "--quiet"]
    if codepeer:
        fullopt += ["--codepeer=on"]
    if replay and not benchmark_mode():
        fullopt += ["--replay"]

    if level is None:
        # If no proof level is specified, we use the default timeout and
        # step limit unless otherwise specified.
        if steps is None:
            steps = max_steps
        if vc_timeout is None:
            vc_timeout = get_default_timeout()
    else:
        fullopt += ["--level=%u" % level]

    if steps is not None:
        fullopt += ["--steps=%d" % steps]
    if memlimit is not None:
        fullopt += ["--memlimit=%d" % memlimit]
    if vc_timeout is not None:
        fullopt += ["--timeout=%d" % vc_timeout]

    if mode is not None:
        fullopt += ["--mode=%s" % (mode)]
    fullopt += ["-j%d" % (procs)]
    if prover:
        prover_arg = build_prover_switch(prover)
    else:
        prover_arg = []
    if benchmark_mode():
        fullopt += ["--benchmark"]
        prover_arg = build_prover_switch([benchmark_mode()])
    fullopt += prover_arg
    if counterexample is not None:
        if not counterexample or benchmark_mode():
            fullopt += ["--counterexamples=off"]
        else:
            fullopt += ["--counterexamples=on", "--ce-steps=5000"]
    if check_counterexamples is not None:
        if check_counterexamples:
            fullopt += ["--check-counterexamples=on"]
        else:
            fullopt += ["--check-counterexamples=off"]
    if why3server_mode():
        fullopt += ["--why3-server=" + why3server_mode()]
    # Add opt last, so that it may include switch -cargs
    if opt is not None:
        fullopt += opt
    report = report if report is not None else "all" if replay else "provers"
    # limit-switches don't play well with sarif output for now
    has_limit_switch = any("--limit" in s for s in fullopt)

    # Build refiners from boolean flags if not explicitly provided
    if refiners is None:
        refiners = build_refiners_from_flags(
            no_fail=no_fail,
            filter_sparklib=filter_sparklib,
            sort_output=sort_output,
            filter_output=filter_output,
            do_sarif_check=enable_sarif_check and not sparklib and not has_limit_switch,
            report=report,
        )

    gnatprove(
        fullopt,
        no_output=no_output,
        refiners=refiners,
        cache_allowed=cache_allowed,
        exit_status=exit_status,
        ada=ada,
        sparklib=sparklib,
        report=report,
        sparklib_bodymode=sparklib_bodymode,
        cwd=cwd,
        timeout=timeout,
        logger=logger,
    )
    verify_counterexamples(cwd=cwd, logger=logger)


def do_flow(
    opt=None,
    procs=parallel_procs,
    no_fail=False,
    mode="all",
    gg=True,
    sort_output=True,
    refiners=None,
    ada=default_ada,
    sparklib=False,
    report=None,
    enable_sarif_check=False,
    cwd=None,
    timeout=None,
    logger=None,
):
    """
    Call gnatprove with standard options for flow. We do generate verification
    conditions, but we don't actually try very hard to prove anything.

    Boolean parameters (sort_output, no_fail, enable_sarif_check) are provided
    for YAML compatibility. They are converted to refiners internally by prove_all.

    Advanced users can pass a custom refiners list to override all boolean flags.
    When refiners is not None, all boolean flags are ignored.

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """

    if not gg:
        if opt is None:
            opt = []
        opt.append("--no-global-generation")

    prove_all(
        opt,
        procs=procs,
        steps=1,
        counterexample=False,
        prover=["cvc5"],
        no_fail=no_fail,
        mode=mode,
        sort_output=sort_output,
        refiners=refiners,
        ada=ada,
        sparklib=sparklib,
        report=report,
        enable_sarif_check=enable_sarif_check,
        cwd=cwd,
        timeout=timeout,
        logger=logger,
    )


def do_flow_only(
    opt=None,
    procs=parallel_procs,
    no_fail=False,
    ada=default_ada,
    logger=None,
):
    """
    Similar to do_flow, but we disable VCG. Should only be used for flow
    tests that take an undue amount of time.
    """

    do_flow(opt, procs, no_fail, mode="flow", ada=ada, logger=logger)


def no_crash(
    sparklib=False,
    opt=None,
    sparklib_bodymode=False,
    cwd=None,
    timeout=None,
    logger=None,
):
    """
    Only attempt to detect crashes and other unexpected behavior. No expected
    tool output is filed for such tests.

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """
    if benchmark_mode():
        prove_all(
            sparklib=sparklib,
            sparklib_bodymode=sparklib_bodymode,
            cwd=cwd,
            timeout=timeout,
            logger=logger,
        )
    else:
        gnatprove(
            no_output=True,
            exit_status=0,
            sparklib=sparklib,
            opt=opt,
            sparklib_bodymode=sparklib_bodymode,
            cwd=cwd,
            timeout=timeout,
            logger=logger,
        )


def clean(cwd=None, timeout=None, logger=None):
    """Call gnatprove with standard options to clean proof artifacts

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """
    prove_all(opt=["--clean"], no_fail=True, cwd=cwd, timeout=timeout, logger=logger)


def to_list(arg):
    """Convert to list

    If arg is already a list, return it unchanged. Otherwise, if it is
    None, return an empty list. In any other case, wrap the argument in
    a list (that contains, as a consequence, only one element).
    """
    if arg is None:
        return []
    elif isinstance(arg, list):
        return arg
    else:
        return [arg]


def grep(regex, strlist, invert=False):
    """Filter a string list by a regex

    PARAMETERS
    regex: a string encoding a regular expression, using python regex syntax
    strlist: a list of strings
    invert: if false, select strings that do *not* match
    """
    p = re.compile(regex)
    return [line for line in strlist if matches(p, line, invert)]


def touch(fname, times=None, cwd=None):
    """touch a file so that it appears altered

    PARAMETERS
    fname: a string corresponding to a filename
    times: optional paramter so set the access time
    cwd: base directory for relative filenames
    """
    path = _resolve_path(fname, cwd)
    with open(path, "a"):
        os.utime(path, times)


def is_windows_platform():
    """Returns True on Windows and False otherwise"""
    platform = sys.platform
    return platform.startswith("win") or platform.startswith("cygwin")


def sleep_on_windows(secs=3):
    """If on Windows then sleep to stabilise the filesystem status

    PARAMETERS
    secs: number of seconds to sleep if in Windows
    """
    if is_windows_platform():
        sleep(secs)


def check_all_spark(result_file, expected_len, cwd=None):
    """Using a gnatprove result file, check that all subprograms, entries, task
       bodies and packages of that unit are in SPARK. Also check that there are
       as many entries as expected.

    PARAMETERS
        result_file      the file to read (relative to cwd if not absolute)
        expected_len     the number of entities expected
    RESULT
        none

    """
    path = _resolve_path(result_file, cwd)
    with open(path, "r") as f:
        result = json.load(f)
        spark_result = result["spark"]
        assert len(spark_result) == expected_len
        for entry in spark_result.values():
            assert entry == "all"


def check_spec_spark(result_file, expected_len, cwd=None):
    """Using a gnatprove result file, check that all specs of that unit
       are in SPARK. Also check that there are as many entries as expected.

    PARAMETERS
        result_file      the file to read (relative to cwd if not absolute)
        expected_len     the number of entities expected
    RESULT
        none
    """
    path = _resolve_path(result_file, cwd)
    with open(path, "r") as f:
        result = json.load(f)
        spark_result = result["spark"]
        assert len(spark_result) == expected_len
        for entry in spark_result.values():
            assert entry == "spec"


def check_trace_files(only_flow=False, cwd=None, logger=None):
    # Note that in order for check_trace_files to work, we have to call one of
    # the other functions first. Otherwise, no trace files will have been
    # generated.

    base = _base_path(cwd)

    # Create a list that contains all trace files lying under directory
    # gnatprove.
    if only_flow:
        trace_dir = base / "gnatprove"
        trace_files = (
            list(trace_dir.glob("*__flow__*.trace")) if trace_dir.exists() else []
        )
        # ??? The above pattern might also match non-flow traces created for a
        # unit with "flow" in its name, but the glob routine accepts only
        # simple patterns and not arbitrary regular expressions, so we can't do
        # better; however, this pacricular name is unlikely to happen in our
        # testsuite.
    else:
        trace_dir = base / "gnatprove"
        trace_files = list(trace_dir.glob("*.trace")) if trace_dir.exists() else []

    log(logger, "Trace files' contents:")
    # Dump the contents of all trace files on stdout
    for trace_file in sorted(trace_files):
        cat(str(trace_file), cwd=None, logger=logger)


def check_output_file(sort=False, cwd=None, logger=None):
    """Print content of output file gnatprove.out.

    The goal is to make this output independent from the order of provers
    used. In particular, the summary table may contain different percentages
    for the provers used to prove the VCs, and the columns of the table may
    be aligned differently due to that. Likewise, the log file may contain
    different timings for the most difficult checks to prove.

    To avoid such differences:
    - replace all sequences of spaces by a single space
    - replace all sequences of '-' characters by a single one
    - filter out substrings starting with '(<provername>', up
      to the following closing parenthesis.
    - replace substring 'proved in max nnn seconds' to hide the actual number
      nnn under the fixed string 'nnn'

    This ensures a common output whatever the order of provers used.
    """

    filename = _resolve_path(os.path.join("gnatprove", "gnatprove.out"), cwd)
    prover_tag = re.compile(
        r"(^.*)(\((CVC4|altergo|Z3|colibri|Trivial|Interval|CVC5)[^\)]*\))(.*$\n)"
    )
    max_time = re.compile(r"(^.*proved in max )[1-9][0-9]*( seconds.*$\n)")
    output = ""

    if not filename.exists():
        log(logger, f"Error: {filename!s} not found")
        return

    with open(filename, "r") as f:
        for line in f:
            m = re.match(prover_tag, line)
            mt = re.match(max_time, line)
            if m:
                newline = m.group(1) + " " + m.group(4)
            elif mt:
                newline = mt.group(1) + "nnn" + mt.group(2)
            else:
                newline = line
            # Replace multiple white spaces by a single one, and multiple
            # '-' characters (used for the frame of the summary tablen, whose
            # size varies depending on prover order) by a single one.
            output += re.sub(" +", " ", re.sub("-+", "-", newline))
    if sort:
        log_sorted(logger, str.splitlines(output))
    else:
        log(logger, output)


def sparklib_exec_test(
    project_file="test.gpr", binary="./obj/test", cwd=None, logger=None
):
    cov_mode = coverage_mode()
    if cov_mode:
        run_command(
            ["gnatcov", "instrument", "-P", project_file, "--level=stmt"], cwd=cwd
        )
    opt = ["-P", project_file]
    if cov_mode:
        opt += ["--src-subdirs=gnatcov-instr", "--implicit-with=gnatcov_rts.gpr"]
    gprbuild(opt=opt, logger=logger, cwd=cwd)
    p = run_command([binary], cwd=cwd)
    log(logger, p.out)


def print_version(cwd=None, logger=None):
    """Print the output of "gnatprove --version".

    Typical output is like this:
      $ gnatprove --version
      <gnatprove version>
      <full-path-to-prover> : <version output for prover>
    Z3 output looks like this:
      Z3 version <bla> - 64 bit
    We remove:
    - the gnatprove version, which changes too much
    - the prover locations
    - platform (32bits/64bits) in Z3 output
    """

    # We remove LD_LIBRARY_PATH which is set by the GNAT compiler dependency.
    # In this way we can test if the provers work without this env var.
    # ??? os.unsetenv didn't work, so setting to empty string instead
    os.environ["LD_LIBRARY_PATH"] = ""

    p = run_command(["gnatprove", "--version"], cwd=cwd)
    lines = p.out.splitlines()
    # drop first line of output
    lines = lines[1:]
    for line in lines:
        # remove everything before the colon, to remove path info
        # there might be no colon, but the code still works
        elts = line.split(":")
        text = elts[-1]

        # remove everything after " - ", to remove mention of platform in z3
        # output
        elts = text.split(" - ")
        text = elts[0]
        log(logger, text)


def run_spark_for_gnattest_json(
    project_file,
    filename,
    line,
    gnattest_JSON,
    cwd=None,
    timeout=None,
    logger=None,
):
    """
    Run gnatprove on the given subprogram with counterexample candidates from
    gnattest.

    Note: The timeout parameter is *reserved* for usage by the testing
    framework. If set and the timeout is exceeded TimeoutExpired exception is
    raised. Do *not* pass this argument explicitly from test.py. Use the
    'timeout' setting in test.yaml instead.
    """
    gnatprove(
        opt=[
            f"-P{project_file}",
            "--quiet",
            "--output=oneline",
            "--counterexamples=on",
            "--check-counterexamples=on",
            "--level=2",
            f"--limit-subp={filename}:{line}",
            f"--gnattest-values={gnattest_JSON}",
        ],
        report=None,
        cwd=cwd,
        timeout=timeout,
        logger=logger,
    )


def flow_gg(opt=None):
    if opt is None:
        opt = []
    opt += ["--flow-show-gg", "--no-inlining"]
    do_flow(
        opt=opt,
        refiners=default_refiners_no_sort() + [GeneratedContractsRefiner()],
    )
