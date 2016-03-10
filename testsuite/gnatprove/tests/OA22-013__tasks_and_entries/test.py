from test_support import *
import re, os

do_flow()

# grep for lines that start with "F ", which correspond to subprogram calls
hand = open(os.path.join("gnatprove", "p.ali"))
for line in hand :
    line = line.rstrip()
    if re.search('^F ', line) :
        print line
