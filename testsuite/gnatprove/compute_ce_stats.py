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
    "./out_20220921_cvc5",
    "./out_20220921_cvc4",
    "./out_20220921_z3",
    "./out_20220930_cvc5",
    "./out_20221115_cvc5",
    "./out_20230131_master",
    "./out_20230202_merge",
]
export_file = "./data.csv"
export_file_incomplete_small_step = "./data_incomplete_small_step.csv"
export_file_incomplete_giant_step = "./data_incomplete_giant_step.csv"

rx_verdict = r"VERDICT: (?P<v>[A-Z_]*), Reason: (?P<r>.*)\| "
rx_small = r"Small-step: (?P<s>[A-Z_]*), Reason: (?P<sr>.*)\| "
rx_giant = r"Giant-step: (?P<g>[A-Z_]*), Reason:(?P<gr>.*)\n"
rx = re.compile(rx_verdict + rx_small + rx_giant)

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
    "no subprogram body": re.compile(r"(.*)Body for subprogram(.*)is not in SPARK"),
    "small-step RAC incomplete": re.compile(r"(.*)normal RAC incomplete(.*)"),
    "constraint error": re.compile(r"(.*)access check failed(.*)"),
    "no giant-step RAC": re.compile(r"(.*)No giant-step result(.*)"),
    "check missing for giant-step RAC": re.compile(
        r"(.*)Giant-step RAC failed but the check is missing(.*)"
    ),
    "out of fuel": re.compile(r"(.*)out of fuel(.*)"),
    "stack overflow": re.compile(r"(.*)Stack overflow(.*)"),
    "protected component or part of variable": re.compile(
        r"(.*)protected component or part of variable(.*)"
    ),
    "expr with private type": re.compile(r"(.*)expr with private type(.*)"),
    "no reason": re.compile(r""),
}
rx_dict_not_checked = {
    "checking not requested": re.compile(
        r"(.*)Counterexample checking not requested(.*)"
    ),
    "no counterexample": re.compile(r"(.*)No counterexample(.*)"),
}
list_of_verdicts = [
    "NOT_CHECKED",
    "INCOMPLETE",
    "NON_CONFORMITY",
    "BAD_COUNTEREXAMPLE",
    "NON_CONFORMITY_OR_SUBCONTRACT_WEAKNESS",
    "SUBCONTRACT_WEAKNESS",
]


def _parse_line(line):
    match = rx.search(line)
    if match:
        return match
    return None


def _parse_reason(reason, rx_dict):
    for key, rx in rx_dict.items():
        match = rx.search(reason)
        if match:
            return key
    print("WARNING! Unknown reason: " + reason)
    return reason


def _add_reason(res, reason, rx_dict):
    if res in ["RES_FAILURE", "RES_NORMAL", "RES_STUCK"]:
        return res
    elif res in ["RES_INCOMPLETE", "RES_NOT_EXECUTED"]:
        return res + " " + _parse_reason(reason, rx_dict)
    else:
        print("WARNING! Unknown RAC result: " + res)
        return res


def parse_file(filepath, data, dir):
    with open(filepath, "r") as file_object:
        line = file_object.readline()
        while line:
            match = _parse_line(line)
            if match is not None:
                verdict = match.group("v")
                reason = match.group("r")
                small_step = match.group("s")
                giant_step = match.group("g")
                small_step_reason = match.group("sr")
                giant_step_reason = match.group("gr")
                if verdict in list_of_verdicts:
                    if verdict == "NOT_CHECKED":
                        verdict = (
                            verdict + " " + _parse_reason(reason, rx_dict_not_checked)
                        )
                        small_step = _add_reason(
                            small_step, small_step_reason, rx_dict_incomplete
                        )
                        giant_step = _add_reason(
                            giant_step, giant_step_reason, rx_dict_incomplete
                        )
                    else:
                        small_step = _add_reason(
                            small_step, small_step_reason, rx_dict_incomplete
                        )
                        giant_step = _add_reason(
                            giant_step, giant_step_reason, rx_dict_incomplete
                        )
                else:
                    print("WARNING! Unknown verdict: " + verdict)
                data.append(
                    {
                        "date": dir,
                        "verdict": verdict,
                        "small_step": small_step,
                        "giant_step": giant_step,
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

agg_data_incomplete_small_step = (
    data.query('verdict == "INCOMPLETE"')
    .groupby("date")["small_step"]
    .value_counts()
    .rename("nb")
)
agg_data_incomplete_small_step = pd.DataFrame(agg_data_incomplete_small_step)
agg_data_incomplete_small_step.to_csv(
    export_file_incomplete_small_step, mode="w", header=True
)

agg_data_incomplete_giant_step = (
    data.query('verdict == "INCOMPLETE"')
    .groupby("date")["giant_step"]
    .value_counts()
    .rename("nb")
)
agg_data_incomplete_giant_step = pd.DataFrame(agg_data_incomplete_giant_step)
agg_data_incomplete_giant_step.to_csv(
    export_file_incomplete_giant_step, mode="w", header=True
)
