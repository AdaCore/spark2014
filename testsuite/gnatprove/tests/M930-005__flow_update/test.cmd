gnatprove -P test.gpr --mode=flow --warnings=on -f -q -u update_legal.adb
gnatprove -P test.gpr --mode=flow --warnings=on -f -q -u update_legal_2.adb
gnatprove -P test.gpr --mode=flow --warnings=on -f -q -u update_legal_3.adb
gnatprove -P test.gpr --mode=flow --warnings=on -f -q -u update_legal_4.adb
gnatmake -gnata main.adb
main
