#!/usr/bin/env python3

"""
Processes a JUnit XML file to check if all successful test cases
are under a specified time threshold.

This script generates a new JUnit XML file containing a single
test case ("AllTestsWithinThreshold"). This test case:
- SUCCEEDS if all passed tests in the input file are *under* the threshold.
- FAILS if any passed test in the input file is *at or over* the threshold.

Failed, errored, and skipped tests from the input file are ignored.

Exit codes:
- 0: All successful tests are under the threshold.
- 1: Some successful tests are at or over the threshold.
- 2: An unexpected error occurred during processing.
- Other non-zero codes may occur in unexpected error situations.
"""

import argparse
import xml.etree.ElementTree as ET
import sys
import time
from typing import List, Tuple


def process_junit(
    input_file: str, threshold: float
) -> Tuple[List[Tuple[str, str, float]], float]:
    """
    Parses the input JUnit XML, checks test times against the threshold.

    Args:
        input_file: Path to the source JUnit XML file.
        threshold: The time in seconds. Tests at or above this are "slow".

    Returns:
        A tuple containing:
        - A list of (classname, name, time) tuples for slow tests.
        - The total time of all processed (passed) tests.
    """
    slow_tests: List[Tuple[str, str, float]] = []
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

        if test_time >= threshold:
            name = testcase.get("name", "UnknownTest")
            classname = testcase.get("classname", "UnknownClass")
            slow_tests.append((classname, name, test_time))

    return slow_tests, total_checked_time


def generate_output_xml(
    output_file: str,
    slow_tests: List[Tuple[str, str, float]],
    script_time: float,
    threshold: float,
):
    """
    Generates the new single-case JUnit XML file based on the analysis.

    Args:
        output_file: Path to write the new XML file.
        slow_tests: The list of slow tests. If empty, the new test case passes.
        script_time: The total running time of this script to report in the output XML.
        threshold: The threshold that was used for the check.
    """
    num_failures = 1 if slow_tests else 0

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
        name="AllTestsWithinThreshold",
        time=str(script_time),
    )

    if slow_tests:
        # The test failed. Create a <failure> element.
        failure_message_lines = [
            (
                f"Test failed: {len(slow_tests)} successful test(s) met"
                f" or exceeded the {threshold}s threshold."
            )
        ]

        for _classname, name, time_val in slow_tests:
            failure_message_lines.append(f"  - {name}: {time_val}s")

        failure_message = "\n".join(failure_message_lines)

        failure_element = ET.SubElement(
            testcase,
            "failure",
            message="One or more tests exceeded the performance threshold.",
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
            "or longer will be flagged."
        ),
    )

    args = parser.parse_args()

    start_time = time.time()

    try:
        slow_tests, _ = process_junit(args.input_file, args.threshold)

        script_elapsed = time.time() - start_time

        generate_output_xml(
            args.output_file, slow_tests, script_elapsed, args.threshold
        )

        if slow_tests:
            print(
                f"Performance check FAILED. {len(slow_tests)}"
                " test(s) exceeded threshold."
            )
            print(f"Report written to {args.output_file}")
            # Exit with a non-zero status code to signal failure to CI/CD systems
            sys.exit(1)
        else:
            print("Performance check PASSED. All tests under threshold.")
            print(f"Report written to {args.output_file}")
            sys.exit(0)

    except Exception as e:
        print(f"An unexpected error occurred: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
