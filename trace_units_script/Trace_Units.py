#! /usr/bin/env python
#Takes as arguments a list of files and/or directories.
#If no arguments are presented, then it assumes that the
#argument is the current path ('.').

from os  import path, walk
from sys import argv
import re

if len(argv) == 1:
    #If no arguments were given, recursively search the current directory.
    print "No arguments were given. Searching under current directory."
    print #Add a blank line.
    argv.append(".")

#Initialize lists to empty.
test_case_files = []
rst_files       = []

for i in range(1, len(argv)):
    if path.isdir(argv[i]):
        #If argument is a directory.
        for r,d,f in walk(argv[i]):
            for files in f:
                if re.search ("\.ad[abs]$", files, re.I):
                    #If it ends in ".ads", ".adb" or ".ada".
                    test_case_files.append(path.join(r,files))
                elif files.endswith(".rst"):
                    rst_files.append(path.join(r,files))
    elif path.isfile(argv[i]):
        #If argument is a file.
        if re.search ("\.ad[abs]$", argv [i], re.I):
            #If it ends in ".ads", ".adb" or ".ada".
            if argv[i].startswith("./") or argv[i].startswith("/"):
                #If file starts with "./" or "/" then we just append it.
                test_case_files.append(argv[i])
            else:
                #If file does not start with "./" or "/" then we put
                #"./" before it.
                test_case_files.append("./" + argv[i])
        elif argv[i].endswith(".rst"):
            #If it ends in ".rst".
            if argv[i].startswith("./") or argv[i].startswith("/"):
                #If file starts with "./" or "/" then we just append it.
                rst_files.append(argv[i])
            else:
                #If file does not start with "./" or "/" then prepend "./"
                rst_files.append("./" + argv[i])
    else:
        #Argument is neither a file, nor a directory.
        continue


test_case_files       = list(set(test_case_files)) #Remove duplicates.
test_case_trace_units = []                         #Initialize to empty.
for i in range(len(test_case_files)):
    #Go through files in the list and extract TUs.
    lines = []
    fd = open(test_case_files[i], "rU") #Open file descriptor.
    lines = fd.read().splitlines()      #Read all lines.
    fd.close()                          #Close file descriptor.

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
                    trace_unit = trace_unit + " " + \
                        re.sub("^ *-- *", "", lines[line + j])
                    j = j + 1
                #Remove spaces from the beginning.
                trace_unit = re.sub("^ *", "", trace_unit)
                #Remove trailing spaces.
                trace_unit = re.sub(" *$", "", trace_unit)
                #Ensure all spaces are single spaces.
                trace_unit = re.sub(" +", " ", trace_unit)
                #Ignore the numbering that is at the front.
                trace_unit = re.sub("^[0123456789]+\.", "", trace_unit)
                test_case_trace_units.append \
                (test_case_files[i] + ":" + str(line + 1) + " " + trace_unit)

#Remove duplicates.
test_case_trace_units = list(set(test_case_trace_units))
rst_files             = list(set(rst_files))

#Initialize lists to empty.
rst_trace_units                   = []
proof_checked_trace_units         = []
front_end_checked_trace_units     = []
flow_analysis_checked_trace_units = []
spark_filter_checked_trace_units  = []
covered_by_another_trace_units    = []
not_tested_trace_units            = []
uncategorised_trace_units         = []
for i in range(len(rst_files)):
    #Go through files in the list and extract TUs.
    lines = []
    fd = open(rst_files[i], "rU")  #Open file descriptor.
    lines = fd.read().splitlines() #Read all lines.
    fd.close()                     #Close file descriptor.

    for line in range(len(lines)):
        #For every line in lines.
        if re.search("^ *.. *_tu-", lines[line], re.I):
            #Create TU by picking up everything between this and the
            #following "_tu-" or by picking up everything between this
            #"_tu-" and the following "_etu-".
            trace_unit = ""
            j = 1
            while line + j < len(lines) \
            and not re.search("_[e]?tu-", lines[line + j], re.I):
                #Continue adding lines to the TU until we either reach
                #the last line or we find a line that contains either
                #of the strings "_tu-" or "_etu-".
                trace_unit = trace_unit + " " + lines[line + j]
                j = j + 1
            #Remove spaces from the beginning.
            trace_unit = re.sub("^ *", "", trace_unit)
            #Remove spaces from the end.
            trace_unit = re.sub(" *$", "", trace_unit)
            #Ensure all spaces are single spaces.
            trace_unit = re.sub(" +", " ", trace_unit)
            #Ignore the numbering that is at the front.
            trace_unit = re.sub("^[0123456789]+\.", "", trace_unit)

            rst_trace_units.append \
            (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            #Do the categorization.
            if re.search("-cbatu-", lines[line], re.I):
                #Add TU to the list of TUs covered by other TUs.
                covered_by_another_trace_units.append \
                (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            elif re.search("-nt-", lines[line], re.I):
                #Add TU to the list of non-tested TUs.
                not_tested_trace_units.append \
                (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            elif re.search("-pr-", lines[line], re.I) \
            or re.search("-fe-", lines[line], re.I) \
            or re.search("-fa-", lines[line], re.I) \
            or re.search("-sf-", lines[line], re.I):
                #Find which tool has to check this TU.
                if re.search("-pr-", lines[line], re.I):
                    #TU has to be checked by proof.
                    proof_checked_trace_units.append \
                    (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
                if re.search("-fe-", lines[line], re.I):
                    #TU has to be checked by the front-end.
                    front_end_checked_trace_units.append \
                    (rst_files[i] + ":" +  str(line + 1) + " " + trace_unit)
                if re.search("-fa-", lines[line], re.I):
                    #TU has to be checked by flow analysis.
                    flow_analysis_checked_trace_units.append \
                    (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
                if re.search("-sf-", lines[line], re.I):
                    #TU has to be checked by SPARK filter.
                    spark_filter_checked_trace_units.append \
                    (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)
            else:
                #Uncategorised TU.
                uncategorised_trace_units.append \
                (rst_files[i] + ":" + str(line + 1) + " " + trace_unit)

#Now the test_case_trace_units and rst_trace_units lists are populated.

#Find orphan TUs.
orphans = [] #Initialize orphans list to empty.
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

#Find barren trace units and create a csv file that contains in each
#line, a TU followed by the test cases that address it.
barren = []
fd = open("traces.csv", "w") #Open file descriptor.

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

fd.close() #Close file descriptor.

#Find number of proof checked barren TUs.
proof_checked_barren = []
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
front_end_checked_barren = []
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
flow_analysis_checked_barren = []
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

#Find number of SPARK filter checked barren TUs.
spark_filter_checked_barren = []
for trace_unit in spark_filter_checked_trace_units:
    dont_care, search_for = trace_unit.split(" ", 1)
    found = 0

    for i in test_case_trace_units:
        dont_care, compare_against = i.split(" ", 1)
        if search_for == compare_against:
            found = 1
            break

    if not found:
        spark_filter_checked_barren.append(trace_unit)

#Print number of total TUs found in ".rst" files.
print "Found", len(rst_trace_units), "TUs in total."

#Print number of barren "PR", "FE", "FA" and "SF" checked TUs.
print "Proof checked TUs covered:", \
len (proof_checked_trace_units) - len (proof_checked_barren), \
"/", len (proof_checked_trace_units)

print "Front-End checked TUs covered:", \
len (front_end_checked_trace_units) - len (front_end_checked_barren), \
"/", len (front_end_checked_trace_units)

print "Flow analysis checked TUs covered:", \
len (flow_analysis_checked_trace_units) - len (flow_analysis_checked_barren), \
"/", len (flow_analysis_checked_trace_units)

print "SPARK filter checked TUs covered:", \
len (spark_filter_checked_trace_units) - len (spark_filter_checked_barren), \
"/", len (spark_filter_checked_trace_units)

#Print number of "covered by other TUs","untested TUs" and "uncategorised TUs".
print "Number of TUs covered by other TUs:", \
len (covered_by_another_trace_units)

print "Number of untested/untestable TUs:", len (not_tested_trace_units)

print "Number of uncategorised TUs:", len (uncategorised_trace_units)

#Print orphans (if they exist).
if len(orphans) > 0:
    print "Found", len(orphans), "orphan TUs:"
    for trace_unit in orphans:
        print trace_unit
    print #Put a blank line between orphans and barren.

#Print barren units (if they exist).
if len(barren) >0 :
    print "Found", len(barren), "barren TUs:"
    for trace_unit in barren:
        print
        print trace_unit
