gcc -c global_illegal.ads
gcc -c global_illegal_2.adb
gnatprove -P test.gpr -f -q -u global_illegal_3.adb
