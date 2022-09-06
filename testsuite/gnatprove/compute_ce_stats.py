#!/usr/bin/env python

# Helper script to compute statistics about checking counterexamples.

# - For each directory in directories, it parses the files *.out to
#   extract information about verdicts for counterexamples.
# - Data is then aggregated to compute the number of VC for a given
#   verdict, and exported to a .csv file for further analysis.

import os
import pandas as pd
import re

# Each one of these directories corresponds to the folder out/
# obtained after having launched the testsuite (locally or on a
# mailserver).
directories = [
    "./out_20220623_fix_verdict_cvc4",
    "./out_20220704_reactivation_cvc5",
    "./out_20220704_reactivation_cvc4",
    "./out_20220704_reactivation_z3",
    "./out_20220728_cvc5",
    "./out_20220728_cvc4",
    "./out_20220728_z3",
]
export_file = "./data.csv"

rx = re.compile(r"VERDICT: (?P<v>[A-Z_]*), Reason: (?P<r>.*)\| Small.*\n")


def _parse_line(line):
    match = rx.search(line)
    if match:
        return match
    return None


rx_dict_incomplete = {
    "cannot decide": re.compile(r"(.*)cannot be evaluated(.*)"),
    "cannot import": re.compile(r"(.*)cannot import value(.*)"),
    "missing return value": re.compile(r"(.*)missing value for return value(.*)"),
    "missing variable value": re.compile(r"(.*)missing value for variable(.*)"),
    "missing parameter value": re.compile(
        r"(.*)No counterexample value for program parameter(.*)"
    ),
    "unsupported": re.compile(r"(.*)not supported(.*)"),
    "no VC": re.compile(r"(.*)No VC(.*)"),
    "no body": re.compile(r"(.*)No body(.*)"),
    "giant-step RAC not executed": re.compile(r"(.*)giant-step RAC not executed(.*)"),
    "small-step RAC incomplete": re.compile(r"(.*)normal RAC incomplete(.*)"),
    "constraint error": re.compile(r"(.*)access check failed(.*)"),
}
rx_dict_not_checked = {
    "checking not requested": re.compile(
        r"(.*)Counterexample checking not requested(.*)"
    ),
    "no counterexample": re.compile(r"(.*)No counterexample(.*)"),
}


def _parse_reason(reason, rx_dict):
    for key, rx in rx_dict.items():
        match = rx.search(reason)
        if match:
            return key
    return None


def parse_file(filepath, data, dir):
    with open(filepath, "r") as file_object:
        line = file_object.readline()
        while line:
            match = _parse_line(line)
            if match is not None:
                verdict = match.group("v")
                reason = match.group("r")
                if verdict == "INCOMPLETE":
                    key = _parse_reason(reason, rx_dict_incomplete)
                    if key is not None:
                        reason = key
                elif verdict == "NOT_CHECKED":
                    key = _parse_reason(reason, rx_dict_not_checked)
                    if key is not None:
                        reason = key
                elif verdict == "BAD_COUNTEREXAMPLE":
                    reason = ""
                elif verdict == "NON_CONFORMITY":
                    reason = ""
                elif verdict == "NON_CONFORMITY_OR_SUBCONTRACT_WEAKNESS":
                    reason = ""
                elif verdict == "SUBCONTRACT_WEAKNESS":
                    reason = ""
                data.append(
                    {
                        "date": dir,
                        "verdict": verdict + " " + reason,
                    }
                )
            line = file_object.readline()


data = []
for dir in directories:
    print(dir)
    for filename in os.listdir(dir):
        f = os.path.join(dir, filename)
        if os.path.isfile(f):
            if f.endswith(".out"):
                parse_file(f, data, dir)
data = pd.DataFrame(data)
agg_data = data.groupby("date")["verdict"].value_counts().rename("nb")
agg_data = pd.DataFrame(agg_data)
agg_data.to_csv(export_file, mode="w", header=True)
