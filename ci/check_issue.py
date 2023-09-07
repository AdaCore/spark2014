from gitlab import Gitlab
from e3.auth.gitlab import gen_gitlab_token
import os
import re

gitlab_project_path = os.environ["CI_PROJECT_PATH"]
gitlab_merge_request_iid = os.environ["CI_MERGE_REQUEST_IID"]

issue_regex = re.compile(r"[^\s]+#[0-9]+")
no_issue_check_regex = re.compile(r"no-issue-check")


gl = Gitlab(
    url="https://gitlab.adacore-it.com",
    private_token=gen_gitlab_token()["token"],
)
project = gl.projects.get(gitlab_project_path)
mr = project.mergerequests.get(gitlab_merge_request_iid)

issues = issue_regex.findall(mr.description)
if len(issues) > 0:
    print(issues)
    exit(0)

if no_issue_check_regex.search(mr.description):
    print("did not find issues, but found no-issue-check")
    exit(0)

print("Did not find any issue number in merge description")
exit(1)
