from test_support import *
import glob

prove_all(opt=["-u", "update_examples.adb"])
prove_all(opt=["-u", "loop_var_loop_invar.adb"])
prove_all(opt=["-u", "reverse_ord.adb"])
prove_all(opt=["-u", "up_timer.adb"])
prove_all(opt=["-u", "f.adb"])
prove_all(opt=["-u", "param_1_illegal.adb"])
prove_all(opt=["-u", "param_1_legal.adb"])
prove_all(opt=["-u", "anti_aliasing.adb"])
prove_all(opt=["-u", "multiple_ports.ads"])
prove_all(opt=["-u", "refined_global_examples.adb"])
prove_all(opt=["-u", "refined_depends_examples.adb"])
prove_all(opt=["-u", "stacks_1.adb"])
prove_all(opt=["-u", "stacks_2.adb"])
prove_all(opt=["-u", "externals.adb"])
prove_all(opt=["-u", "hal.adb"])
gcc("main_hal.adb")
prove_all(opt=["-u", "inter_unit_elaboration_examples.adb"])
prove_all(opt=["-u", "intra_unit_elaboration_order_examples.adb"])
prove_all(opt=["-u", "initialization_and_elaboration.adb"])

# copy traces produced for f.adb to standard output
files = glob.glob("gnatprove/f*.trace")
for file in files:
   cat (file)
