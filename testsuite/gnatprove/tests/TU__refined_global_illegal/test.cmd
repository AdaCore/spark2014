gcc -c refined_global_illegal.adb
gnatprove -P test.gpr -q -f -u refined_global_illegal_2.adb
