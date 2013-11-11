gnatprove -P test.gpr -f -q -u proof_in_legal.adb
gnatprove -P test.gpr -f -q -u proof_in_illegal.adb
gnatprove -P test.gpr --ide-progress-bar -f -q -u proof_in_illegal_2.adb
