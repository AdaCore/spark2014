gnatprove -P test.gpr --warnings=on --report=all -f -q -u update_legal.adb
gnatprove -P test.gpr --warnings=on --report=all -f -q -u update_uninitialized.adb
gnatprove -P test.gpr --warnings=on --report=all -f -q -u update_uninitialized_2.adb
gnatprove -P test.gpr --warnings=on --report=all -f -q -u update_uninitialized_3.adb
gnatmake -gnata main.adb
main
