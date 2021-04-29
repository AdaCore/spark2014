from e3.os.process import Run
import re

timeout_reg = re.compile ("--timeout (\d+)")
steps_reg = re.compile ("--steps (\d+)")
memlimit_reg = re.compile ("--memlimit (\d+)")
prover_reg = re.compile ("--prover ([^ ]+)")
proof_reg = re.compile ("--proof ([^ ]+)")
counterexample_reg = re.compile ("--counterexample ([^ ]+)")

def extract_value(regex, s):
    """regex is a compiled regex that has a subgroup. Search for the regex in s
    and return the value for the subgroup. Return None if no match was found."""
    m = regex.search(s)
    if m:
        return m.group(1)
    else:
        return None

def some_None(a, b, c, d, e, f):
    """return True if some values are None"""
    return ((a is None) or (b is None) or (c is None) or (d is None) or (e is None) or (f is None))

def all_None(a, b, c, d, e, f):
    """return True if all values are None"""
    return ((a is None) and (b is None) and (c is None) and (d is None) and (e is None) and (f is None))

def get_or_check_level_info(info, string):
    """extract info about steps, timeout, etc from the [string]. If the string
       contains no such info, do nothing. If the string contains only partial
       info, report and stop. If [info] contains already some data, the data
       extracted from the string should be identical. If [info] doesn't contain
       any data, the info from the string will be stored in [info]."""
    my_timeout = extract_value(timeout_reg, string)
    my_steps = extract_value(steps_reg, string)
    my_memlimit = extract_value(memlimit_reg, string)
    my_prover = extract_value(prover_reg, string)
    my_proof = extract_value(proof_reg, string)
    my_counterexample = extract_value(counterexample_reg, string)
    if all_None(my_timeout, my_steps, my_memlimit, my_prover, my_proof, my_counterexample):
        return
    if some_None(my_timeout, my_steps, my_memlimit, my_prover, my_proof, my_counterexample):
        print("partial setting of values detected:")
        print(string)
        exit(0)
    if info["timeout"]:
        #checking mode
        if info["timeout"] == my_timeout and\
            info["steps"] == steps and\
            info["memlimit"] == my_memlimit and\
            info["prover"] == my_prover and\
            info["proof"] == my_proof and\
            info["counterexample"] == my_counterexample:
            return
        else:
            print("detected different settings across lines")
            print("collected from some previous line:")
            print(info)
            print("current line:")
            print(string)
            print(my_timeout, my_steps, my_memlimit, my_prover, my_proof, my_counterexample)
            exit(0)
    else:
        info["timeout"] = my_timeout
        info["steps"] = my_steps
        info["memlimit"] = my_memlimit
        info["prover"] = my_prover
        info["proof"] = my_proof
        info["counterexample"] = my_counterexample


def print_info(info):
    """custom printing routine to fix ordering of fields while printing"""
    print("timeout:" + info["timeout"] + ", steps:" + info["steps"] +
          ", memlimit:" + info["memlimit"] + ", prover:" + info["prover"] +
          ", proof:" + info["proof"] + ", counterexample:" + info["counterexample"])

def run_level_test(level):
    process = Run(["gnatprove", "-P", "test.gpr", "-d", "--level="+str(level)])
    info = {"timeout"        : None,
            "steps"          : None,
            "memlimit"       : None,
            "prover"         : None,
            "proof"          : None,
            "counterexample" : None}
    strlist = str.splitlines(process.out)
    for line in strlist:
        get_or_check_level_info(info, line)
    print_info(info)


print("level 0:")
run_level_test(0)
print("level 1:")
run_level_test(1)
print("level 2:")
run_level_test(2)
print("level 3:")
run_level_test(3)
print("level 4:")
run_level_test(4)
