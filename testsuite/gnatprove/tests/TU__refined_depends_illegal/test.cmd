gcc -c refined_depends_illegal.adb
gnatprove -P test.gpr --warnings=on -q -f -u refined_depends_illegal_2.adb
