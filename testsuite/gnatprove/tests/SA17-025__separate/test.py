from test_support import *

# prove file should work when specifying the separate
# right now it proves the entire unit "pack"
print "=========== prove file ============="
prove_all(opt=["pack-p.adb"])
# prove subprogram should only prove the subprogram in pack-p.adb
print "=========== prove subprogram ============="
prove_all(opt=["pack-p.adb", "--limit-subp=pack-p.adb:2"])
# prove line should only prove the specified line
print "=========== prove line ============="
prove_all(opt=["pack-p.adb", "--limit-line=pack-p.adb:13"])
print "=========== prove check ============="
prove_all(opt=["pack-p.adb", "--limit-line=pack-p.adb:13:19:VC_ASSERT"])
print "=========== prove region ============="
prove_all(opt=["pack-p.adb", "--limit-region=pack-p.adb:12:13"])
