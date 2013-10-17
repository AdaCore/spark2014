gcc -c initializes_illegal.adb
gcc -c initializes_illegal_2.ads
gcc -c initializes_illegal_3.ads
gnatprove -P test.gpr -f -q -u initializes_illegal_4.adb
gcc -c initializes_illegal_5.adb
gnatprove -P test.gpr -f -q -u initializes_illegal_6.adb
