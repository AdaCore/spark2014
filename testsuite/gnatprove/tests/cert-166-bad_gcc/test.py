from test_support import prove_all, is_windows_platform, TESTDIR
import os
import sys

# Create path to the fake broken compiler. GPR requires an absolute path,
# which depends on where this test is instantiated.

platform = sys.platform
if is_windows_platform():
    bad_gnat_exec = "bad-gcc.bat"
else:
    bad_gnat_exec = "bad-gcc"

bad_gnat_path = TESTDIR + os.sep + bad_gnat_exec

with open("test.gpr", "w") as f:
    f.write("project Test is\n")
    f.write("   package Compiler is\n")
    f.write('   for Driver ("Ada") use "' + bad_gnat_path + '";\n')
    f.write("   end Compiler;\n")
    f.write("end Test;")

prove_all()
