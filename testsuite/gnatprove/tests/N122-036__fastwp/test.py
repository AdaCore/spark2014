#!/usr/bin/env python

import glob
import os.path
import tools

# list_of_files = glob.glob ("*.mlw")
list_of_files = [
   "app.mlw",
   "result.mlw",
   "call.mlw",
   "assert.mlw",
   "if.mlw",
   "raise.mlw",
   "try.mlw",
   "assign.mlw",
   "call_exc.mlw",
   "abstract.mlw",
   "any.mlw",
   "loop.mlw",
   "bug1.mlw",
   "bug2.mlw",
   "bug3.mlw",
   "bug4.mlw",
   "bug5.mlw",
   "bug6.mlw",
   "bug7.mlw",
   "variant.mlw",
   "rec_variant.mlw",
   "case.mlw",
   "for.mlw",
   "field_assign.mlw",
   "fwp.mlw"
   ]

def compute_expected_output(fn, outputfile):
    """
    Find in file fn all occurrences of an expected result, which takes the form
    of a line "(* Valid *)" or "(* Unknown *)", and print the corresponding
    result ("Valid" or "Unknown" without the quotes) in file outputfile.
    """
    test = open(fn, "r")
    inp = test.readlines()
    output = tools.grep ("\(\* (\w*) \*\)", inp)
    tools.save_to_file (outputfile, output)

def main():
    for fn in list_of_files:
        basename = os.path.splitext(fn)
        basename = basename[0]
        xoutfile = basename + ".actout"
        exp_output = basename + ".out"
        # Run why on fn and extract the actual output
        output = tools.run_why (fn)
        pattern = fn + ".*: (.+) \(.*\)"
        output = tools.grep (pattern, output)
        tools.save_to_file (xoutfile, output)
        # Extract the expected output from fn
        compute_expected_output(fn, exp_output)
        # Issue a message "OK" if actual and expected output coincide, and a
        # message "DIFF" otherwise.
        if tools.diff (exp_output, xoutfile) == 0:
            print fn, " : OK"
        else:
            print fn, " : DIFF"
        os.remove (xoutfile)
        os.remove (exp_output)

if __name__ == "__main__":
    main()
