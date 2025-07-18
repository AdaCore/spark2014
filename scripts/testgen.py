import os
import sys
import json
import argparse
import subprocess


def run_spark(project_file, filename, line):
    print("Running gnatprove")
    subprocess.run(
        [
            "gnatprove",
            f"-P{project_file}",
            "-j0",
            "--output=oneline",
            "-u",
            "--counterexamples=on",
            "--check-counterexamples=on",
            "--level=2",
            f"--limit-subp={filename}:{line}",
        ]
    )


def run_gnattest(project_name, filename, line):
    print(f"Running gnattest at {(filename)}:{str(line)}")
    subprocess.run(
        [
            "gnattest",
            f"-P{project_name}",
            filename,
            f"--gen-test-subprograms={filename}:{str(line)}",
            "--gen-test-vectors",
            "--gen-test-num=1",
        ]
    )


def get_hash(project_name, filename, line):
    print(
        f"Retrieving {project_name} subprogram's hash16 at "
        + f"{(filename)}:{str(line)}"
    )

    command = ["gnattest", f"-P{project_name}", f"--dump-subp-hash={filename}:{line}"]

    process = subprocess.run(command, capture_output=True, text=True)

    return process.stdout.strip("\n").strip("\t")


def get_values_from_spark_JSON(JSON_file, source_file, source_line):
    print(f"Retrieving counter-example's values from {os.path.abspath(JSON_file)}.")
    try:
        with open(JSON_file, "r") as f:
            data = json.load(f)

            proofs = data.get("proof", {})
            for proof in proofs:

                cntexmp_value = proof.get("cntexmp_value", {})

                subp_file = cntexmp_value.get("subp_file")
                subp_line = cntexmp_value.get("subp_line")

                if subp_file == source_file and str(subp_line) == source_line:
                    return cntexmp_value.get("inputs", {})

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


def get_subprogram(JSON_file):
    print(
        "Retrieving subprogram's declaration location from "
        + f"{os.path.abspath(JSON_file)}"
    )
    try:
        with open(JSON_file, "r") as f:
            data = json.load(f)

            flows = data.get("flow", {})

            for flow in flows:
                if flow.get("rule", {}) == "SUBPROGRAM_TERMINATION":

                    filename = flow.get("file", {})
                    line = flow.get("line", {})

                    return [filename, line]

            sys.exit("error: subprogram not found.")

    except FileNotFoundError:
        print(f"Error: filename  {JSON_file}  not found.")
        return None
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON format in {JSON_file}.")
        return None
    except Exception as e:
        print(f"An unexpected error occurred: {e}")
        return None


def replace_values(JSON_file, subp_hash, values):
    print(f"Replacing gnattest values by SPARK's in {os.path.abspath(JSON_file)}.")
    try:
        with open(JSON_file, "r") as f:
            data = json.load(f)

            subprogram = data.get(subp_hash, {})

            if subprogram == {}:
                sys.exit("error: hashes do not match")  # This should never happen

            test_vectors = data.get(subp_hash, {}).get("test_vectors", {})

            param_vectors = test_vectors[0].get("param_values", {})

            for value in values:
                name = value.get("name", {})
                val = value.get("value", {})

                for param in param_vectors:
                    if param.get("name", {}) == name:
                        param["value"] = val

        with open(JSON_file, "w") as f:
            json.dump(data, f, indent=4)

    except FileNotFoundError:
        print(f"Error: filename {JSON_file} not found.")
        return None
    except json.JSONDecodeError:
        print(f"Error: Invalid JSON format in {JSON_file}.")
        return None


def generate_tests(project_name, filename, line):
    print("Generating tests")
    subprocess.run(
        [
            "gnattest",
            f"-P{project_name}",
            f"--gen-test-subprograms={filename}:{str(line)}",
        ]
    )


def run(project_file, filename, line):
    project_path = os.path.dirname(os.path.realpath(project_file))

    os.chdir(project_path)

    # SPARK step

    run_spark(project_file, filename, line)

    spark_filenames = []

    for file in os.listdir(os.path.join(project_path, "obj/gnatprove/")):
        if file.endswith(".spark"):
            spark_filenames.append(file)

    if spark_filenames == []:
        sys.exit("could not find generated .spark file.")

    ce_values = None
    for spark_filename in spark_filenames:
        ce_values = get_values_from_spark_JSON(
            os.path.join(project_path, "obj/gnatprove/", spark_filename), filename, line
        )
        if ce_values is not None:
            break

    if ce_values is None:
        sys.exit("no counter-example at " + filename + ":" + line)

    print(f"counter-example values: {str(ce_values)}")

    # gnattest step

    [project_name, _] = [s for s in project_file.split(".") if s.strip()]

    hash_value = get_hash(project_name, os.path.join("src/", filename), line)

    run_gnattest(project_name, filename, line)

    replace_values(
        os.path.join(
            project_path,
            "obj",
            "gnattest",
            "tests",
            "JSON_Tests",
            f"{project_name}.json",
        ),
        hash_value,
        ce_values,
    )

    generate_tests(project_name, filename, line)

    print(
        "tests have been generated and can be found at "
        + f"{os.path.abspath(project_path + "/obj/gnattest/tests/")}"
    )

    # run tests

    os.chdir("obj/gnattest/harness")

    subprocess.run("make")

    subprocess.run(["./test_runner", f"--routines={filename}:{str(line)}"])


def main():
    parser = argparse.ArgumentParser(
        prog="Testgen",
        description="Generate a ADA test harness from gnatprove's counter-exemples",
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

    args = parser.parse_args()

    project_path = args.project_file
    [filename, line] = [s for s in args.position.split(":") if s.strip()]

    run(project_path, filename, line)


if __name__ == "__main__":
    main()
