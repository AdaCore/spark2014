gnatprove -P test.gpr -f -q --warnings=on --report=all -u init.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u init_2.ads
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initializes_legal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initializes_illegal.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initializes_illegal_2.adb
gnatprove -P test.gpr -f -q --warnings=on --report=all -u initializes_illegal_3.ads

