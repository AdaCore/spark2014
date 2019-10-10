from test_support import *

# This function edit the session by replacing the lines corresponding to the
# failing coq proof (contains keyword edited="file.vc") with one that contains
# a correct coq proof. (-> "result status = Valid"). We can then check that the
# proof remains proven in the last run of prove_all.
def edit_session():
    session = "proof/sessions/greatest_common_divisor__g_c_d/why3session.xml"
    content = ""
    with open(session, 'r') as file:
        for current_line in file.readlines():
            # We detect the end of the Coq filename
            if current_line.rfind ('.v"') >= 0:
                current_line = re.sub (r'<result status.*/>', '<result status="valid" time="1.23"/>', current_line)
            content = content + current_line
    with open(session, 'w') as file:
        file.write(content)


prove_all(counterexample=False)
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=greatest_common_divisor.adb:10"], counterexample=False, filter_output=".*Grammar extension")
print "======================================="
edit_session()
print "======================================="
prove_all(counterexample=False)
