gcc -c loop_related_illegal.adb
gnatprove -P test.gpr --warnings=on -q -f -u loop_related_illegal_2.adb
gnatprove -P test.gpr --mode=flow -q -f -u loop_related_illegal_3.adb
gnatmake -q -gnata main.adb
main
gnatmake -q -gnata main2.adb
main2
