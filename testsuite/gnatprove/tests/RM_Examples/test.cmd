gnatprove -P test.gpr -f -q --warnings=on --report=all -u update_examples.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u loop_var_loop_invar.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all --steps=10000 -u reverse_ord.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u up_timer.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u f.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u param_1_illegal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u param_1_legal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u anti_aliasing.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u multiple_ports.ads
gnatprove -P test.gpr -f -q --warnings=on --report=all -u refined_global_examples.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u refined_depends_examples.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u stacks_1.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u stacks_2.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all --mode=flow -u externals.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all --mode=flow -u hal.adb
gcc -c main_hal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u inter_unit_elaboration_examples.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u intra_unit_elaboration_order_examples.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initialization_and_elaboration.adb
