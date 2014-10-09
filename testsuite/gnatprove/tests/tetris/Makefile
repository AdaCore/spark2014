.PHONY: check flow integrity functional clean

$(shell mkdir -p obj)

check:
	gnatprove -P tetris.gpr --mode=check -u tetris_initial.adb

flow:
	gnatprove -P tetris.gpr --mode=flow -u tetris_flow.adb

integrity:
	gnatprove -P tetris.gpr --mode=prove -u tetris_integrity.adb

functional:
	gnatprove -P tetris.gpr --mode=all -u tetris_functional.adb

clean:
	gnatprove -P tetris.gpr --clean
