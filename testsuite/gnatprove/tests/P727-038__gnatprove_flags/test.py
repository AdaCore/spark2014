from test_support import *

# This test is intended to clarify how -u and -U work.
#
# foo is a main unit and depends on bar.
# baz depends on nothing.

basic_options = ["-P", "test.gpr", "-f", "-q",
                 "--report=all", "--prover=altergo", "--output=brief"]

print("--- Messages on foo and bar should appear")
gnatprove(opt=basic_options)

print("-" * 60)
print("--- Messages on foo only should appear")
gnatprove(opt=basic_options + ["-u", "foo.adb"])

print("-" * 60)
print("--- Messages on foo and bar should appear")
gnatprove(opt=basic_options + ["foo.adb"])

print("-" * 60)
print("--- Messages on foo, bar, baz should appear")
gnatprove(opt=basic_options + ["-U"])
