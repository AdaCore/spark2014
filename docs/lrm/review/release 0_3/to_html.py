#!/usr/bin/env python

import cgi
import os
import re
import sys

from optparse import OptionParser

from tn_lib import parse_tn

def fmt(s):
    s = s.strip()
    return cgi.escape(s)

def fmt_ml(s):
    #return "<br>\n".join(fmt(s).replace(" ", "&nbsp").splitlines())
    return "<br>\n".join(fmt(s).splitlines())

def show_token(filename):
    fd = open(filename, "rU")
    info = parse_tn(filename, fd.read())
    fd.close()

    print "<h1>%s</h1>" % fmt(filename)

    print "<h2>Outstanding review comments</h2>"
    for comment in info["comments"]:
        if len(comment["checked by"].strip()) > 0:
            c_status = "resolved"
        elif len(comment["action taken"].strip()) > 0:
            c_status = "addressed"
        else:
            c_status = "todo"

        if c_status == "resolved":
            continue

        print "<h3>%s</h3>" % fmt(comment["label"])

        print "<table class='%s'>" % c_status
        print ("<tr><td>Location:</td><td class='raw'>%s</td></tr>" %
               fmt(comment["location"]))
        print ("<tr><td>Description:</td><td class='raw'>%s</td></tr>" %
               fmt_ml(comment["description"]))
        print ("<tr><td>Action:</td><td class='raw'>%s</td></tr>" %
               fmt_ml(comment["action taken"]))
        print ("<tr><td>Checked by:</td><td class='raw'>%s</td></tr>" %
               fmt(comment["checked by"]))
        print "</table>"

def main():
    op = OptionParser()

    options, args = op.parse_args()

    print "<html>"
    print "<head>"
    print "<style>"
    print "td.raw { font-family: monospace; }"
    print "td { vertical-align: top; }"
    print "table.todo td { background-color: #fcc; }"
    print "table.addressed td { background-color: #ffc; }"
    print "table.resolved td { background-color: #cfc; }"
    print "</style>"
    print "</head>"
    print "<body>"
    for filename in args:
        show_token(filename)
    print "</body>"
    print "</html>"

if __name__ == "__main__":
    main()
