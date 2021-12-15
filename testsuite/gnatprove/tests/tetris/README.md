This program implements a simple version of the game of Tetris. An invariant of
the game is stated in function `Valid_Configuration`, that all procedures of
the unit must maintain. This invariant depends on the state of the game which
if updated by every procedure. Both the invariant and the state of the game are
encoded as Ghost Code. The invariant expresses two properties:

- A falling piece never exits the game board, and it does not overlap with
  pieces that have already fallen.

- After a piece has fallen, the complete lines it may create are removed from
  the game board.

GNATprove proves all checks on the full version of this program found in
`tetris_functional.adb`. Intermediate versions of the program show the
initial code without any contracts in `tetris_initial.adb`, the code with
contracts for data dependencies in `tetris_flow.adb` and the code with
contracts to guard against run-time errors in `tetris_integrity.adb`. The
complete program, including the BSP to run it on the ATMEL SAM4S board, is
available on the [AdaCore
blog](http://blog.adacore.com/tetris-in-spark-on-arm-cortex-m4).
