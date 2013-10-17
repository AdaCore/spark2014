gcc -c external_variables_legal.ads
gcc -c externals.adb
gcc -c hal.adb main.adb
gnatprove -P test.gpr -f -q -u volatiles_legal.adb
