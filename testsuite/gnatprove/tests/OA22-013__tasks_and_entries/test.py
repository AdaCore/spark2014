from test_support import *
import re, os

do_flow()

hand = open(os.path.join("gnatprove", "p.ali"))
for line in hand :
    line = line.rstrip()
    if re.search('^F ', line) :
        print line
