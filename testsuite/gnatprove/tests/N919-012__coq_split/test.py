from test_support import *
import xml.etree.ElementTree as ET

def check_session_file():
    sessionfile = "proof/sessions/greatest_common_divisor__g_c_d/why3session.xml"
    tree = ET.parse(sessionfile)
    root = tree.getroot()
    # magic XPath string to check whether the manual proof is at the expected
    # place. This will return a list of matched xml elements. As the search
    # string matches exactly the required element, if the search contains one
    # element we are good. if it is empty, we have a problem.
    manual_proof = root.findall("./file/theory[@name='Greatest_common_divisor__g_c_d__subprogram_def']/goal/transf/goal/transf/goal/proof/path[@name='Greatest_common_divisor__g_c_d__pragargs__cmp.v']")
    assert len(manual_proof) == 1, "did not find manual proof at correct place"

prove_all(opt=['--proof=progressive'], counterexample=False)
print("=======================================")
prove_all(prover=["coq"], opt=["--limit-line=greatest_common_divisor.ads:10", "--proof=progressive"], counterexample=False, filter_output=".*Grammar extension")
print("=======================================")
check_session_file()
