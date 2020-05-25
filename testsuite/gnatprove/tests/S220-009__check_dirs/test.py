from test_support import *

sys.stdout = open('result1', 'w')

# This filter out only the lines that do not begin with "Changing" (?! is
# negative lookahead).
prove_all(opt=["--verbose", "--debug", "--prover=coq",
               "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"],
          steps=None, counterexample=False, filter_output="(?!^Changing)")

result = open ('result1', 'r')
sys.stdout = sys.__stdout__

count_lines = 0
count = 0
list_dir = []

# This counts the number of Changing directory.
# It also checks that two directories change are exactly the same (should be
# call to gnatwhy3).
for l in result:
    count_lines += 1
    m = re.search(r':.*$', l)
    if m.group(0) is None:
        print("TODO error")
    # Check that the exact same directory occurs at least twice
    if m.group(0) in list_dir:
        count += 1
    list_dir.append(m.group(0))


print("Number of lines changing to a directory")
print count_lines

if count == 1:
    print("Two change directory are exactly same (probably call to gnatwhy3)")
