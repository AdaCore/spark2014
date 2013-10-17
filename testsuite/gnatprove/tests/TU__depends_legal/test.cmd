gcc -c depends_legal.ads
gnatprove -P test.gpr --mode=flow -f -q -u depends_legal_2.adb
