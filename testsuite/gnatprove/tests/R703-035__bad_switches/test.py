from test_support import *

print "===== expecting message for unrecognized switch ====="
gnatprove(opt=["-P", "bad_global.gpr"])
print "===== expecting message for unrecognized switch ====="
gnatprove(opt=["-P", "bad_global2.gpr"])
print "===== expecting message for not allowed switch ====="
gnatprove(opt=["-P", "bad_global3.gpr"])
print "===== expecting message for not allowed switch ====="
gnatprove(opt=["-P", "bad_global4.gpr"])
print "===== expecting message for unrecognized switch ====="
gnatprove(opt=["-P", "bad_fs.gpr"])
print "===== expecting message for not allowed switch ====="
gnatprove(opt=["-P", "bad_fs2.gpr"])
print "===== expecting message for unknown file ====="
gnatprove(opt=["-P", "bad_fs3.gpr"])
