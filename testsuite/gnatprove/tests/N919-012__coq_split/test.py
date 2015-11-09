from test_support import *
from time import sleep
import xml.etree.ElementTree as ET

conf_file = "test.whyconf"

def check_session_file():
    sessionfile = "proof/sessions/greatest_common_divisor/why3session.xml"
    tree = ET.parse(sessionfile)
    root = tree.getroot()
    # magic XPath string to check whether the manual proof is at the expected
    # place. This will return a list of matched xml elements. As the search
    # string matches exactly the required element, if the search contains one
    # element we are good. if it is empty, we have a problem.
    manual_proof = root.findall("./file/theory[@name='Greatest_common_divisor__g_c_d__subprogram_def']/goal/transf/goal/transf/goal/proof[@edited]")
    assert len(manual_proof) == 1, "did not find manual proof at correct place"

write_why3_config_file_with_coq(conf_file)
prove_all(opt=['--proof=progressive'], counterexample=False)
print "======================================="
prove_all(prover=["coq"], opt=["--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.ads:10", "--proof=progressive"], counterexample=False)
print "======================================="
check_session_file()
