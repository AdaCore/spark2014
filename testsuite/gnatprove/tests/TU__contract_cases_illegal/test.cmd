gcc -c contract_cases_illegal.ads
gnatprove -P test.gpr -f -q -u contract_cases_illegal_2.adb
gnatmake -gnata -q main.adb
gnatmake -gnata -q main2.adb
main
main2
