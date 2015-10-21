from test_support import *

conf_file = "test.whyconf"

def edit_session():
    session = "proof/sessions/greatest_common_divisor/why3session.xml"
    with open(session, 'r') as file:
        content = file.read()
    content = str.replace(content, "<unedited/>", '<result status="valid" time="1.23"/>')
    with open(session, 'w') as file:
        file.write(content)


write_why3_config_file_with_coq(conf_file)
prove_all(counterexample=False)
print "======================================="
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.adb:10"], counterexample=False)
print "======================================="
edit_session()
print "======================================="
prove_all(counterexample=False)
