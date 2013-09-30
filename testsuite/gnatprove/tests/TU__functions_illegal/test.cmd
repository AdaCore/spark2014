gcc -c functions_illegal.adb
gnatprove -P test.gpr -f -q -u functions_illegal_2.adb
