import sys
import os
from datetime import datetime

usage = """ IMPORTANT: THIS IS HOW TO USE THIS SCRIPT
This script only works with LINUX !
To use this script, you should use a useless sandbox: ie you would be fine
with it being destroyed.
To create this sandbox, you can follow the wiki:
"deploy-anod-sandbox -v wave my_useless_sandbox"
In this sandbox, you should install spark2014 *and* work in a terminal where
you set the environment of this sandbox.
"./bin/anod -v install spark2014"
"eval `./bin/anod setenv spark2014`"

USAGE:
python bisect.py path_to_my_sandbox my_test_command d1 d2

[path_to_my_sandbox]: The path to your useless sandbox. Be careful, this path
will be used for installation of spark2014 and removal of spark2014.
[my_test_command]: A command that can be run in terminal whose output you can
look at to know if the build is good or not. For example, I used:
"gnatprove -P temp/tmp-test-S726-006/src/test.gpr --debug --prover=cvc4 -f"
[d1]: The last time you know the test was good
[d2]: The first time you know the test was bad

EXAMPLE of execution of the script:
'python bisect.py "PATH/sandbox_wave/sandbox_wave" "gnatprove -P TEST/tmp-test-S726-006/src/test.gpr --debug --prover=cvc4 -f" 20180202 20190720' # noqa

During execution of the script you will be asked y/n question to execute unsafe
commands (such as rm -rf spark2014). You will also be asked if the output is
good bad or skip:
- skip means that there was an error not linked to your test.
- bad means this is still in regression (same state as today build)
- good means this is the expected output

IMPORTANT: You can always exit with Ctrl-C
"""

# Path to the bin/anod inside the sandbox
bin_exe = ""
# Command for the test to be launched
test_cmd = ""


def yes_no_message(text, valid, invalid, skip=""):
    """ choice message: returns either valid, invalid or skip text provided. It
        is repeated until the user manage to select one of the three. """
    print text
    m = raw_input()
    if m == valid:
        return m
    else:
        if m == invalid:
            return m
        else:
            if m == skip:
                return m
            else:
                yes_no_message(text, valid, invalid, skip)


def get_version(sandbox_dir):
    """ Some checks on the sandbox used: this returns the version from
        sandbox.yaml or exit if none is found."""
    sandboxyaml = os.path.join(sandbox_dir, "meta/sandbox.yaml")
    if os.path.exists(sandboxyaml):
        f = open(sandboxyaml, "r")
        for i in f:
            if 'setup_name' in i:
                f.close()
                return i
        f.close()
        print "Problem while detecting the version: check sandbox.yaml is ok"
        print ("sandbox.yaml located at: \n" + sandboxyaml)
        exit(1)


def test_correct_sandbox_dir(sandbox_dir):
    joined_path = os.path.realpath(os.path.join(sandbox_dir, "bin/anod"))
    if os.path.exists(joined_path):
        print (joined_path + " is ok.")
        print ("version is: " + get_version(sandbox_dir))
        return joined_path
    else:
        print "[bisect]:Appending bin/anod should be a valid anod file"
        print (joined_path + " is not a valid anod file")
        exit(1)


def test_date(date_as_input):
    """ Return a python date from the user input date."""
    if len(date_as_input) != 8:
        print "[bisect]: This date should be YYYYMMDD with 8 figures"
        print date_as_input
        exit(1)
    else:
        try:
            year = int(date_as_input[:4])
            month = int(date_as_input[4:6])
            day = int(date_as_input[6:8])
        except Exception:
            print "[bisect]: Provided dates should all be integers"
            exit(1)
        return (datetime(year, month, day))


def get_middle(first_date, last_date):
    mid_date = first_date + (last_date - first_date) / 2
    # Truncate to the days
    mid_date = datetime(mid_date.year, mid_date.month, mid_date.day)
    return mid_date


def real_bisect(date_last_good, date_first_bad, test_current_date):
    """ This is the real bisecting function. It tests the date in the middle of
        the two given date. It looks at user feedback to continue recursively
        on a new halved range. """
    assert (date_last_good <= date_first_bad)
    mid_date = get_middle(date_last_good, date_first_bad)
    if mid_date <= date_last_good or mid_date >= date_first_bad:
        print "[bisect]: End of the algorithm"
        print "The last known good is:"
        print date_last_good
        print "The first known bad is:"
        print date_first_bad
    else:
        choice = test_current_date(mid_date)
        if choice == "skip":
            while choice == "skip" and mid_date <= date_first_bad:
                mid_date = get_middle(mid_date, date_first_bad)
                choice = test_current_date(mid_date)
        if choice == "good":  # good
            real_bisect(mid_date, date_first_bad, test_current_date)
        else:
            if choice == "bad":  # bad
                real_bisect(date_last_good, mid_date, test_current_date)
            else:  # skip
                print "[bisect]: This should not be a skip ! Please report !"
                exit(1)


def install_spark(bin_exe, date=""):
    """ This script removes spark2014 then reinstall it with
        --build-date=date"""
    spark_suf = "../../x86_64-linux/spark2014"
    spark_install = os.path.realpath(os.path.join(bin_exe, spark_suf))
    rm_command = "rm -rf " + spark_install
    print (rm_command)
    choice = yes_no_message("WARNING command above will be executed [y/n]",
                            "y",
                            "n")
    if choice:
        os.system(rm_command)
    else:
        print "[bisect]: Check script or report if the rm command looks bad"
        exit(1)
    if date is "":
        execute = bin_exe + " install spark2014"
        print ("[bisect]: Executing: " + execute)
        os.system(execute)
    else:
        execute = bin_exe + " --build-date=" + date + " install spark2014"
        print ("[bisect]: Executing: " + execute)
        os.system(execute)


def convert_date(date):
    """ Take a python date and convert it into a YYYYMMDD"""
    mon = str(date.month)
    # Some dates need to start with 0 such as 4th of August is 0408 not 48
    if len(mon) == 1:
        mon = "0" + mon
    day = str(date.day)
    if len(day) == 1:
        day = "0" + day
    return (str(date.year) + mon + day)


def test(date):
    """ Test on a particular date."""
    global bin_exe
    global test_cmd
    date_format = convert_date(date)
    print "[bisect]: Testing for the following date:"
    print (date_format)
    install_spark(bin_exe, date=date_format)
    print ("[bisect]: Version of gnatprove tested is")
    os.system("gnatprove --version")
    os.system(test_cmd)
    choice = yes_no_message("Is the test ok ? [good/bad/skip]",
                            "good",
                            "bad",
                            "skip")
    return choice


def bisect(sandbox_dir, last_known_good, first_known_bad):
    """ bisect with initial tests and warnings."""
    global bin_exe
    print "[bisect]: testing the sandbox directory"
    bin_exe = test_correct_sandbox_dir(sandbox_dir)

    choice = yes_no_message("Do you want to test the test on current setup ?\
                             [y/n]", "y", "n")
    if choice == "y":
        os.system(test_cmd)
    else:
        print "[bisect]: No initial test done"
    print "[bisect]: Checking the format used for dates"
    date_last_good = test_date(last_known_good)
    date_first_bad = test_date(first_known_bad)
    print "[bisect]: Starting bisection"
    real_bisect(date_last_good, date_first_bad, test)


try:
    arg1, arg2, arg3, arg4 = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    test_cmd = arg2
except Exception as e:
    print "[bisect]: ERROR: Problem with the number of arguments"
    print e
    print usage
    exit(1)

bisect(arg1, arg3, arg4)
