#! /usr/bin/env python
#Takes as arguments a list of files and/or directories.
#If no arguments are presented, then it assumes that the
#argument is the current path ('.').

from os  import path, walk
from sys import argv
import re

if len(argv) == 1:
    #If no arguments were given, we recursively search the current directory.
    print "No arguments were given. Searching under current directory."
    print #Adding a blank line.
    argv.append(".")

test_case_files = [] #Initializing test_case_files list to empty.
rst_files = []       #Initializing rst_files list to empty.

for i in range(1, len(argv)):
    if path.isdir(argv[i]):
        #If argument is a directory.
        for r,d,f in walk(argv[i]):
            for files in f:
                if files.endswith(".ads") or files.endswith(".adb") or files.endswith(".ada"):
                    test_case_files.append(path.join(r,files))
                elif files.endswith(".rst"):
                    rst_files.append(path.join(r,files))
    elif path.isfile(argv[i]):
        #If argument is a file.
        if argv[i].endswith(".ads") or argv[i].endswith(".adb") or argv[i].endswith(".ada"):
            #If it ends in ".ads", ".adb" or ".ada".
            if argv[i].startswith("./") or argv[i].startswith("/"):
                #If file starts with "./" or "/" then we just append it.
                test_case_files.append(argv[i])
            else:
                #If file does not start with "./" or "/" then we put "./" before it.
                test_case_files.append("./" + argv[i])
        elif argv[i].endswith(".rst"):
            #If it ends in ".rst".
            if argv[i].startswith("./") or argv[i].startswith("/"):
                #If file starts with "./" or "/" then we just append it.
                rst_files.append(argv[i])
            else:
                #If file does not start with "./" or "/" then we put "./" before it.
                rst_files.append("./" + argv[i])
    else:
        #Argument is neither a file, nor a directory.
        continue


test_case_files = list(set(test_case_files)) #Removing duplicates from test_case_files.
test_case_trace_units = []                   #Initializing test_case_trace_units list to empty.
for i in range(len(test_case_files)):
    #Going through all files in the list and extracting the trace units.
    lines = []
    fd = open(test_case_files[i], "rU") #Opening file descriptor.
    lines = fd.read().splitlines()      #Reading all lines of the file and storing them in lines.
    fd.close()                          #Closing file descriptor.

    for line in range(len(lines)):
        if lines[line].strip():
            #Not an empty line.
            if re.search("-- *TU *:", lines[line]):
                #Add first line of TU.
                lines[line] = re.sub("-- *TU *:", "-- TU:", lines[line])
                dont_care, trace_unit = lines[line].split("-- TU:", 1)
                #Add subsequent lines of the TU.
                j = 1
                while lines[line + j].strip and \
                re.search("^ *--", lines[line + j]) and \
                (not re.search("-- *TU *:", lines[line + j])):
                    trace_unit = trace_unit + " " + re.sub("^ *-- *", "", lines[line + j])
                    j = j + 1
                #Removing spaces from the beginning.
                trace_unit = re.sub("^ *", "", trace_unit)
                #Removing trailing spaces.
                trace_unit = re.sub(" *$", "", trace_unit)
                #Ensuring that all spaces are single spaces.
                trace_unit = re.sub(" +", " ", trace_unit)
                test_case_trace_units.append(test_case_files[i] + ":" + str(line + 1) + " " + trace_unit)

test_case_trace_units = list(set(test_case_trace_units)) #Removing duplicates from test_case_trace_units.

rst_files = list(set(rst_files))       #Removing duplicates from rst_files.
rst_trace_units = []                   #Initializing rst_trace_units list to empty.
proof_checked_trace_units = []         #Initializing list of proof checked TUs.
front_end_checked_trace_units = []     #Initializing list of Front-End checked TUs.
flow_analysis_checked_trace_units = [] #Initializing list of flow-analysis checked TUs.
covered_by_another_trace_units = []    #Initializing list of TUs that are covered by other TUs.
not_tested_trace_units = []            #Initializing list of TUs that have not been tested.
uncategorised_trace_units = []         #Initializing list of TUs that have not been categorised.
for i in range(len(rst_files)):
    #Going through all files in the list and extracting the trace units.
    lines = []
    fd = open(rst_files[i], "rU")  #Opening file descriptor.
    lines = fd.read().splitlines() #Reading all lines of the file and storing them in lines.
    fd.close()                     #Closing file descriptor.

    for line in range(len(lines)):
        #For every line in lines.
        if re.search("^ *.. *_tu-", lines[line], re.I):
            #Create the TU by picking up everything between this and the following "_tu-"
            #or by picking up everything between this "_tu-" and the following "_etu-".
            trace_unit = ""
            j = 1
            while line + j < len(lines) and not re.search("_tu-", lines[line + j], re.I) \
            and not re.search("_etu-", lines[line + j], re.I):
                #Continue adding lines to the TU until we either reach the last line
                #or we find a line that contains either of the strings "_tu-" and "_etu-".
                trace_unit = trace_unit + " " + lines[line + j]
                j = j + 1
            #Removing spaces from the beginning.
            trace_unit = re.sub("^ *", "", trace_unit)
            #Removing spaces from the end.
            trace_unit = re.sub(" *$", "", trace_unit)
            #Ensuring that all spaces are single spaces.
            trace_unit = re.sub(" +", " ", trace_unit)

            rst_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            #Do the categorization.
            if re.search("-cbatu-", lines[line], re.I):
                #Adding TU to the list of TUs that are covered by other TUs.
                covered_by_another_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            elif re.search("-nt-", lines[line], re.I):
                #Adding TU to the list of TUs that have not been tested.
                not_tested_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            elif re.search("-pr-", lines[line], re.I) or re.search("-fe-", lines[line], re.I) \
            or re.search("-fa-", lines[line], re.I):
                #Find which tool has to check this TU.
                if re.search("-pr-", lines[line], re.I):
                    #TU has to be checked by proof.
                    proof_checked_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
                if re.search("-fe-", lines[line], re.I):
                    #TU has to be checked by the front-end.
                    front_end_checked_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
                if re.search("-fa-", lines[line], re.I):
                    #TU has to be checked by proof.
                    flow_analysis_checked_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            else:
                #Uncategorised TU.
                uncategorised_trace_units.append(rst_files[i] + ":" + str(line + 1) + " " + trace_unit)

#Now the test_case_trace_units and rst_trace_units lists have been populated.

#Find orphan TUs.
orphans = [] #Initializing orphans list to empty.
for trace_unit in test_case_trace_units:
    dont_care, search_for = trace_unit.split(" ", 1)
    found = 0

    for i in rst_trace_units:
        dont_care, compare_against = i.split(" ", 1)
        if search_for == compare_against:
            found = 1
            break

    if not found:
        orphans.append(trace_unit)

#Find barren trace units and create a csv file
#that contains in each line, a TU followed by
#the test cases that address it.
barren = [] #Initializing barren list to empty.
fd = open("traces.csv", "w") #Opening file descriptor.

for trace_unit in rst_trace_units:
    if trace_unit not in not_tested_trace_units and \
    trace_unit not in covered_by_another_trace_units:

        fd.write("\"" + trace_unit + "\"")
        dont_care, search_for = trace_unit.split(" ", 1)
        found = 0

        for i in test_case_trace_units:
            file_and_line, compare_against = i.split(" ", 1)
            if search_for == compare_against:
                fd.write(", \"" + file_and_line + "\"")
                found = 1

        fd.write("\n")

        if not found:
            barren.append(trace_unit)

fd.close() #Closing file descriptor.

#Find number of proof checked barren TUs.
proof_checked_barren = [] #Initializing proof_checked_barren list to empty.
for trace_unit in proof_checked_trace_units:
    dont_care, search_for = trace_unit.split(" ", 1)
    found = 0

    for i in test_case_trace_units:
        dont_care, compare_against = i.split(" ", 1)
        if search_for == compare_against:
            found = 1
            break

    if not found:
        proof_checked_barren.append(trace_unit)

#Find number of front-end checked barren TUs.
front_end_checked_barren = [] #Initializing front_end_checked_barren list to empty.
for trace_unit in front_end_checked_trace_units:
    dont_care, search_for = trace_unit.split(" ", 1)
    found = 0

    for i in test_case_trace_units:
        dont_care, compare_against = i.split(" ", 1)
        if search_for == compare_against:
            found = 1
            break

    if not found:
        front_end_checked_barren.append(trace_unit)

#Find number of flow analysis checked barren TUs.
flow_analysis_checked_barren = [] #Initializing flow_analysis_checked_barren list to empty.
for trace_unit in flow_analysis_checked_trace_units:
    dont_care, search_for = trace_unit.split(" ", 1)
    found = 0

    for i in test_case_trace_units:
        dont_care, compare_against = i.split(" ", 1)
        if search_for == compare_against:
            found = 1
            break

    if not found:
        flow_analysis_checked_barren.append(trace_unit)

#Print number of total TUs found in .rst files
print "Found", len(rst_trace_units), "TUs in total."

#Printing number of barren "PR", "FE" and "FA" checked TUs.
print "Proof checked TUs covered:", len (proof_checked_trace_units) - len (proof_checked_barren), \
"/", len (proof_checked_trace_units)

print "Front-End checked TUs covered:", len (front_end_checked_trace_units) - len (front_end_checked_barren), \
"/", len (front_end_checked_trace_units)

print "Flow analysis checked TUs covered:", len (flow_analysis_checked_trace_units) - len (flow_analysis_checked_barren), \
"/", len (flow_analysis_checked_trace_units)

#Printing number of "covered by other TUs"/"untested TUs"/"uncategorised TUs".
print "Number of TUs covered by other TUs:", len (covered_by_another_trace_units)
print "Number of untested/untestable TUs:", len (not_tested_trace_units)
print "Number of uncategorised TUs:", len (uncategorised_trace_units)

#Print orphans (if they exist).
if len(orphans) > 0:
    print "Found", len(orphans), "orphan TUs:"
    for trace_unit in orphans:
        print trace_unit
    print #Putting one blank line in between orphans and barren.

#Printing barren units (if they exist).
if len(barren) >0 :
    print "Found", len(barren), "barren TUs:"
    for trace_unit in barren:
        print
        print trace_unit
