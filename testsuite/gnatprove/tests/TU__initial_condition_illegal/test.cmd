gcc -c initial_condition_illegal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initial_condition_illegal_2.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initial_condition_illegal_3.adb
