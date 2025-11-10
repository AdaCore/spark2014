from test_support import prove_all, TESTDIR
import os

# Create path to the fake broken compiler. GPR reguired an absolute path,
# which depends on where this test is instantiated.
bad_gnat_path = TESTDIR + os.sep + "bad-gcc"

with open("test.gpr", "w") as f:
    f.write("project Test is\n")
    f.write("   package Compiler is\n")
    f.write('   for Driver ("Ada") use "' + bad_gnat_path + '";')
    f.write("   end Compiler;\n")
    f.write("end Test;")

prove_all()
