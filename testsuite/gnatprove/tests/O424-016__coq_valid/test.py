from test_support import *

def edit_session():
    session = "proof/sessions/greatest_common_divisor/why3session.xml"
    with open(session, 'r') as file:
        content = file.read()
    content = str.replace(content, "<unedited/>", '<result status="valid" time="1.23"/>')
    with open(session, 'w') as file:
        file.write(content)


prove_all(counterexample=False)
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=greatest_common_divisor.adb:10"], counterexample=False, filter_output=".*Grammar extension")
print "======================================="
edit_session()
print "======================================="
prove_all(counterexample=False)
