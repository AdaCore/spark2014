#!/usr/bin/env python

from optparse import OptionParser

def clean_file(filename):
    tmp = []

    fd = open(filename, "rU")
    for raw_line in fd:
        tmp.append(raw_line.split(";", 1)[0].rstrip())
    fd.close()
    tmp.append("")

    fd = open(filename, "w")
    fd.write("\n".join(tmp))
    fd.close()

def main():
    op = OptionParser()

    _, args = op.parse_args()
    map(clean_file, args)

if __name__ == "__main__":
    main()
