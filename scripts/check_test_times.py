#!/usr/bin/env python3

"""
Check successful JUnit test times and generate a single-case JUnit report.

Use --find-too-slow to flag tests at or above the threshold, or --find-too-fast
to flag tests below it as candidates for removing their large marker. Failed,
errored, skipped, and explicitly excluded tests are ignored.

Exit codes:
- 0: No tests were flagged.
- 1: Some successful tests were flagged.
- 2: An unexpected error occurred during processing.
- Other non-zero codes may occur in unexpected error situations.
"""

import argparse
import xml.etree.ElementTree as ET
import sys
import time
from typing import List, Tuple


def process_junit(
    input_file: str, threshold: float, find_too_fast: bool, exclude_tests=()
) -> Tuple[List[Tuple[str, str, float]], float]:
    """
    Parses the input JUnit XML, checks test times against the threshold.

    Args:
        input_file: Path to the source JUnit XML file.
        threshold: The time threshold in seconds.
        find_too_fast: Flag tests below the threshold instead of at or above it.
        exclude_tests: Test names to ignore.

    Returns:
        A tuple containing:
        - A list of (classname, name, time) tuples for flagged tests.
        - The total time of all processed (passed) tests.
    """
    flagged_tests: List[Tuple[str, str, float]] = []
    total_checked_time: float = 0.0

    try:
        tree = ET.parse(input_file)
        root = tree.getroot()
    except ET.ParseError as e:
        print(f"Error parsing XML file {input_file}: {e}", file=sys.stderr)
        raise
    except FileNotFoundError:
        print(f"Error: Input file not found at {input_file}", file=sys.stderr)
        raise

    # Use .//testcase to find all testcase elements regardless of nesting
    for testcase in root.findall(".//testcase"):
        if testcase.get("name") in exclude_tests:
            continue

        # Check if the test was successful
        # A successful test has no <failure>, <error>, or <skipped> child
        is_failure = testcase.find("failure") is not None
        is_error = testcase.find("error") is not None
        is_skipped = testcase.find("skipped") is not None

        if is_failure or is_error or is_skipped:
            continue  # Ignore non-successful tests

        # This is a passed test, check its time
        test_time_str = testcase.get("time")
        if test_time_str is None:
            continue  # Ignore tests without a time attribute

        try:
            test_time = float(test_time_str)
            total_checked_time += test_time
        except ValueError:
            print(
                (
                    "Warning: Skipping testcase with unparseable time:"
                    f"{testcase.get('name')}"
                ),
                file=sys.stderr,
            )
            continue

        flagged = test_time < threshold if find_too_fast else test_time >= threshold
        if flagged:
            name = testcase.get("name", "UnknownTest")
            classname = testcase.get("classname", "UnknownClass")
            flagged_tests.append((classname, name, test_time))

    return flagged_tests, total_checked_time


def generate_output_xml(
    output_file: str,
    flagged_tests: List[Tuple[str, str, float]],
    script_time: float,
    threshold: float,
    find_too_fast: bool,
):
    """
    Generates the new single-case JUnit XML file based on the analysis.

    Args:
        output_file: Path to write the new XML file.
        flagged_tests: The list of flagged tests. If empty, the new test case passes.
        script_time: The total running time of this script to report in the output XML.
        threshold: The threshold that was used for the check.
        find_too_fast: Report candidates for removing the large marker.
    """
    num_failures = 1 if flagged_tests else 0

    # Create the root <testsuites> element
    output_root = ET.Element("testsuites")

    # Create the single <testsuite>
    testsuite = ET.SubElement(
        output_root,
        "testsuite",
        name="PerformanceThresholdCheck",
        tests="1",
        failures=str(num_failures),
        time=str(script_time),
    )

    # Create the single <testcase>
    testcase = ET.SubElement(
        testsuite,
        "testcase",
        classname="PerformanceTests",
        name=(
            "LargeTestsAtOrAboveThreshold"
            if find_too_fast
            else "AllTestsWithinThreshold"
        ),
        time=str(script_time),
    )

    if flagged_tests:
        # The test failed. Create a <failure> element.
        if find_too_fast:
            message = "Consider removing large: true from these tests."
            summary = (
                f"{len(flagged_tests)} successful large test(s) ran below"
                f" the {threshold}s threshold. {message}"
            )
        else:
            message = "One or more tests exceeded the performance threshold."
            summary = (
                f"Test failed: {len(flagged_tests)} successful test(s) met"
                f" or exceeded the {threshold}s threshold."
            )
        failure_message_lines = [summary]

        for _classname, name, time_val in flagged_tests:
            failure_message_lines.append(f"  - {name}: {time_val}s")

        failure_message = "\n".join(failure_message_lines)

        failure_element = ET.SubElement(
            testcase,
            "failure",
            message=message,
        )
        failure_element.text = failure_message

    # Write the new XML to the output file
    try:
        tree = ET.ElementTree(output_root)
        # Pretty-print the XML (requires Python 3.9+ for ET.indent)
        if sys.version_info >= (3, 9):
            ET.indent(tree, space="  ", level=0)

        with open(output_file, "wb") as f:
            tree.write(f, encoding="utf-8", xml_declaration=True)
    except Exception as e:
        print(f"Error writing output file {output_file}: {e}", file=sys.stderr)
        raise


def main():
    """
    Main function to parse arguments and orchestrate the script.
    """
    parser = argparse.ArgumentParser(
        description=(
            "Check JUnit test times against a threshold"
            " and generate a summary report."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("input_file", help="Path to the input JUnit XML file.")
    parser.add_argument(
        "output_file", help="Path to write the new, single-case JUnit XML report."
    )
    parser.add_argument(
        "--threshold",
        type=float,
        required=True,
        help=(
            "Time threshold in seconds. Passed tests taking this long "
            "or longer are flagged with --find-too-slow; tests below this "
            "time are flagged with --find-too-fast."
        ),
    )
    parser.add_argument(
        "--exclude-test",
        action="append",
        default=[],
        help="Ignore this test name (may be repeated).",
    )

    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--find-too-slow",
        action="store_true",
        help="Flag tests at or above the threshold.",
    )
    mode.add_argument(
        "--find-too-fast",
        action="store_true",
        help="Flag fast tests as candidates for removing large: true.",
    )

    args = parser.parse_args()

    start_time = time.time()

    try:
        flagged_tests, _ = process_junit(
            args.input_file, args.threshold, args.find_too_fast, args.exclude_test
        )

        script_elapsed = time.time() - start_time

        generate_output_xml(
            args.output_file,
            flagged_tests,
            script_elapsed,
            args.threshold,
            args.find_too_fast,
        )

        if flagged_tests:
            if args.find_too_fast:
                print(
                    f"Large test check: {len(flagged_tests)} test(s) ran below"
                    f" {args.threshold}s. Consider removing large: true:"
                )
            else:
                print(
                    f"Performance check FAILED. {len(flagged_tests)}"
                    " test(s) exceeded threshold."
                )
            for _classname, name, test_time in flagged_tests:
                print(f"  - {name}: {test_time}s")
            print(f"Report written to {args.output_file}")
            # Exit with a non-zero status code to signal failure to CI/CD systems
            sys.exit(1)
        else:
            if args.find_too_fast:
                print("Large test check PASSED. No reclassification candidates.")
            else:
                print("Performance check PASSED. All tests under threshold.")
            print(f"Report written to {args.output_file}")
            sys.exit(0)

    except Exception as e:
        print(f"An unexpected error occurred: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
