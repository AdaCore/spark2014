# This script calls gnattest on an ADA subprogram to generate test cases
# then feed them to gnatprove for it to try to use them as CE values.

import os
import sys
import json
import argparse
import subprocess


# run spark with --gnattest-values
def run_spark(project_file, filename, line, gnattest_JSON):
    print("Running gnatprove")
    print(project_file, filename, line, gnattest_JSON)
    subprocess.run(
        [
            "gnatprove",
            f"-P{project_file}",
            "-j0",
            "--output=oneline",
            "--counterexamples=on",
            "--check-counterexamples=on",
            "--level=2",
            f"--limit-subp={filename}:{line}",
            f"--gnattest-values={gnattest_JSON}",
        ]
    )


# generate test values with gnattest
def run_gnattest(project_name, filename, line, nb_cases):
    print(f"Running gnattest at {(filename)}:{str(line)}")
    subprocess.run(
        [
            "gnattest",
            f"-P{project_name}",
            filename,
            f"--gen-test-subprograms={filename}:{str(line)}",
            "--gen-test-vectors",
            f"--gen-test-num={nb_cases}",
        ]
    )


# run gnatfuzz with user-handed arguments
def gnatfuzz(subcommand, subsubcommand, project_name, args):
    subprocess.run(
        ["gnatfuzz", subcommand, subsubcommand, f"-P{project_name}.gpr"] + args
    )


# generate 'better' test values with gnatfuzz
def run_gnatfuzz(project_name, sub_id):
    gnatfuzz(
        "fuzz-everything", "test", project_name, [f"--subprogram-ids-to-test={sub_id}"]
    )


# retreive a subprogram's id according to gnatfuzz
def get_subprogram_id(project_name, filename, line):
    print(f"Running gnatfuzz at {(filename)}:{str(line)}")
    gnatfuzz("fuzz-everything", "inspect", project_name, [])

    json_path = os.path.join("obj", "gnatfuzz", "analyze.json")

    try:
        with open(json_path, "r") as f:
            data = json.load(f)

            subp = data.get("fuzzable_subprograms", {})
            for sub in subp:

                start_line = sub.get("start_line", {})
                source_filename = sub.get("source_filename", {})

                if str(start_line) == str(line) and filename in source_filename:
                    return sub.get("id", {})

            return None

    except FileNotFoundError:
        print(f"Error: {json_path} not found.")
        return None
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON format in {json_path}.")
        return None
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        return None


# retreive a subprogram's hash according to gnattest
def get_hash(project_name, filename, line):
    print(
        f"Retrieving {project_name} subprogram's hash16 at "
        + f"{(filename)}:{str(line)}"
    )

    command = ["gnattest", f"-P{project_name}", f"--dump-subp-hash={filename}:{line}"]

    process = subprocess.run(command, capture_output=True, text=True)

    return process.stdout.strip("\n\t")


# extract relevant data from gnattest's json
def get_test_case_from_gnattest(JSON_file, my_hash):
    try:
        with open(JSON_file, "r") as f:
            return json.load(f).get(my_hash, {}).get("test_vectors", {})

        return None

    except FileNotFoundError:
        print(f"Error: filename  {JSON_file}  not found.")
        return None
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON format in {JSON_file}.")
        return None
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        return None


# peform the entire pipeline
def run(project_file, filename, line, nb_tests, gnatfuzz_mode):
    project_path = os.path.dirname(os.path.realpath(project_file))

    os.chdir(project_path)

    [project_name, _] = [s for s in project_file.split(".") if s.strip()]

    hash_value = get_hash(project_name, os.path.join("src/", filename), line)

    run_gnattest(project_name, filename, line, nb_tests)

    if gnatfuzz_mode:
        print("running gnatfuzz")
        subp_id = get_subprogram_id(project_name, filename, line)

        if subp_id is None:
            sys.exit("Subprogram ID not found in gnatfuzz JSON.")

        run_gnatfuzz(project_name, subp_id)

    gnattest_json_path = os.path.join(
        project_path,
        "obj",
        "gnattest",
        "tests",
        "JSON_Tests",
        f"{project_name}.json",
    )

    test_values = get_test_case_from_gnattest(gnattest_json_path, hash_value)

    CE_values_path = os.path.realpath(f"CE_candidates_{hash_value}.json")

    with open(CE_values_path, "w") as f:
        json.dump(test_values, f)

    run_spark(project_file, filename, line, CE_values_path)


def main():
    parser = argparse.ArgumentParser(
        prog="Testgen",
        description="Run gnatprove with CE candidates from gnattest.",
    )

    parser.add_argument(
        "-p",
        help="Path to the project file",
        required=True,
        type=str,
        dest="project_file",
    )

    parser.add_argument(
        "-s",
        help="file:line of the subprogram to generate tests from",
        required=True,
        type=str,
        dest="position",
    )

    parser.add_argument(
        "-n",
        help="number of test cases to generate from gnattest",
        required=True,
        type=int,
        dest="nb_tests",
    )

    parser.add_argument(
        "--use_gnatfuzz",
        help="try to find CE candidates using gnatfuzz and symCC, requires to be in"
        + " a gnatfuzz env",
        required=False,
        type=bool,
        dest="gnatfuzz_mode",
    )

    args = parser.parse_args()

    project_path = args.project_file
    [filename, line] = [s for s in args.position.split(":") if s.strip()]
    nb_tests = args.nb_tests

    if nb_tests < 1:
        sys.exit("-n must be at least 1.")

    run(project_path, filename, line, nb_tests, args.gnatfuzz_mode)


if __name__ == "__main__":
    main()
