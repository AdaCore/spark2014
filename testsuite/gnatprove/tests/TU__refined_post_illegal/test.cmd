gcc -c refined_post_illegal.adb
gnatprove -P test.gpr -q -f -u --warnings=on --report=all refined_post_illegal_2.adb
gnatmake -gnata main
main
gnatmake -gnata main2
main2
