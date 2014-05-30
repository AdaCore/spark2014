import re
import subprocess

why3 = "why3"

def empty_list ():
    return []

def grep(regex, strlist, invert=False):
    """Filter a string list by a regex

       The regex can contain one group, which will be extracted

    PARAMETERS
    regex: a string encoding a regular expression, using python regex syntax
    strlist: a list of strings
    """
    p = re.compile(regex)
    res = []
    for line in strlist:
        m = re.match(p, line)
        if (invert and not m) or (not invert and m):
            try:
                res.append (m.group(1))
            except IndexError:
                res.append (m.group(0))
    return res

def run_why (fn, args=["--prover", "altergo-gp", "--extra-config", "why3.conf", "-t", "1"]):
    proc = [ why3, "--debug", "fast_wp" ]
    proc += args
    proc += [fn]
    output = subprocess.check_output(proc).splitlines()
    return output

def diff (f1, f2):
    proc = ["diff", "-u"]
    proc += [f1, f2]
    return subprocess.call(proc)

def save_to_file(fn, strlist):
    f = open(fn, "w")
    for s in strlist:
        f.write("%s\n" % s)
    f.close()

def print_list (strlist):
    for s in strlist:
        print s
