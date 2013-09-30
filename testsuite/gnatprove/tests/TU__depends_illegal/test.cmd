gcc -c depends_illegal.ads
gcc -c depends_illegal_2.adb
gnatprove -P test.gpr -f -q -u depends_illegal_3.adb
gnatprove -P test.gpr -f -q -u depends_illegal_4.adb
