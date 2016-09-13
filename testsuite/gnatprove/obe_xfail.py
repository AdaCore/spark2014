from subprocess import check_output
import re
import glob
import os.path

# script to be run on a server where bugtool is available

status_re = re.compile(r"Status: (.*)")
TN_re = re.compile(r'[0-9A-Z][0-9A-C][0-9][0-9]-[0-9][0-9][0-9]')
xfail_re = re.compile(r'XFAIL')


def get_tn_info(tn):
    """return the info text for a TN (a string)"""
    return check_output(["bugtool", "info", tn])


def tn_status(tn):
    """return the TN status as a string for a TN"""
    info = get_tn_info(tn)
    m = re.search(status_re, info)
    if m:
        return m.group(1)
    else:
        exit(1)


def tn_is_open(tn):
    """return true when the TN is open"""
    status = tn_status(tn)
    return (status == "open")


def test_is_xfail(testdir):
    """return the list of TNs mentioned in test.opt and test name if the test
       contained in testdir is marked XFAIL on at least one platform. Return
       empty list if the test is XFAIL but there are no such TNs. Return None
       if test is not XFAIL.
    """
    test_opt = os.path.join(testdir, "test.opt")
    if os.path.exists(test_opt):
        with open(test_opt, "r") as f:
            text = f.read()
            m = re.search(xfail_re, text)
            if m:
                l = re.findall(TN_re, text)
                l = l + re.findall(TN_re, testdir)
                return l
            else:
                return None
    else:
        return None


def check_xfail_tests():
    """print a message for all tests that are XFAIL and for which no open TN
       exists.
    """
    tests = glob.glob("tests/*")
    for test in tests:
        xfail_list = test_is_xfail(test)
        if xfail_list is None:
            pass
        elif xfail_list == []:
            print "test %s is XFAIL, but there is no TN" % test
        else:
            all_closed = True
            for tn in xfail_list:
                if tn_is_open(tn):
                    all_closed = False
            if all_closed:
                print "test %s is XFAIL, " % test +\
                    "all associated TNs are not open"


check_xfail_tests()
