from subprocess import check_output
import re
import glob
import os.path

# script to be run on a server where bugtool is available

status_re = re.compile(r"Status: (.*)")
TN_re = re.compile(r"[0-9A-Z][0-9A-C][0-9][0-9]-[0-9][0-9][0-9]")
xfail_re = re.compile(r"XFAIL")
assigned_to = re.compile("Assigned to: (.*)")


def get_tn_info(tn):
    """return the info text for a TN (a string)"""
    return check_output(["bugtool", "info", tn]).decode("utf-8")


def tn_status(tn):
    """return the TN status as a string for a TN"""
    info = get_tn_info(tn)
    m = re.search(status_re, info)
    if m:
        return m.group(1)
    else:
        exit(1)


def tn_assignee(tn):
    info = get_tn_info(tn)
    return re.search(assigned_to, info).group(1)


def tn_is_open(tn):
    """return true when the TN is open"""
    status = tn_status(tn)
    return status == "open"


def test_is_xfail(testdir):
    """return the list of TNs mentioned in test.opt and test name if the test
    contained in testdir is marked XFAIL on at least one platform. Return the
    TN(s) mentioned in the test name first. Return empty list if the test is
    XFAIL but there are no TNs in the name nor the test.opt. Return None if
    test is not XFAIL.
    """
    test_opt = os.path.join(testdir, "test.opt")
    if os.path.exists(test_opt):
        with open(test_opt, "rb") as f:
            text = f.read().decode("utf-8")
            m = re.search(xfail_re, text)
            if m:
                my_list = re.findall(TN_re, text)
                my_list = re.findall(TN_re, testdir) + my_list
                return my_list
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
            print("test %s is XFAIL, but there is no TN" % test)
        else:
            all_closed = True
            for tn in xfail_list:
                if tn_is_open(tn):
                    all_closed = False
            if all_closed:
                assignee = tn_assignee(xfail_list[0])
                print(
                    (
                        f"test {test} is XFAIL, all associated TNs"
                        f"{xfail_list} are not open ({assignee})"
                    )
                )


check_xfail_tests()
