from e3.auth.gitlab import gen_gitlab_token
import gitlab
import glob
import os.path
import re

issue_re = re.compile(r"[A-z0-9/]+#[0-9]+")
numre = re.compile(r"[0-9]+")
xfail_re = re.compile(r"XFAIL")

gl = gitlab.Gitlab(
    url="https://gitlab.adacore-it.com",
    private_token=gen_gitlab_token()["token"],
)


def get_issue(issue):
    project_name, issue_id = issue.split("#")
    project = gl.projects.get(project_name)
    return project.issues.get(issue_id)


def test_is_xfail(testdir):
    """return the list of issues mentioned in test.opt and test name if the
    test contained in testdir is marked XFAIL on at least one platform. Return
    the issue(s) mentioned in the test name first. Return empty list if the
    test is XFAIL but there are no issues in the name nor the test.opt. Return
    None if test is not XFAIL.
    """
    test_opt = os.path.join(testdir, "test.opt")
    if os.path.exists(test_opt):
        with open(test_opt, "rb") as f:
            text = f.read().decode("utf-8")
            m = re.search(xfail_re, text)
            if m:
                my_list = re.findall(issue_re, text)
                testname = os.path.basename(testdir)
                m = re.match(numre, testname)
                if m:
                    my_list = [("eng/spark/spark2014#" + m.group(0))] + my_list
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
    tests += glob.glob("internal/*")
    for test in tests:
        testname = os.path.basename(test)
        xfail_list = test_is_xfail(test)
        if xfail_list is None:
            pass
        elif xfail_list == []:
            print(f"test {testname} is XFAIL, but there is no TN")
        else:
            issues = [get_issue(issue_id) for issue_id in xfail_list]
            all_closed = True

            for issue in issues:
                if issue.state == "opened":
                    all_closed = False
            if all_closed:
                assignee = issues[0].assignee
                print(
                    (
                        f"test {testname} is XFAIL, all associated issues"
                        f"{xfail_list} are not open ({assignee})"
                    )
                )


check_xfail_tests()
