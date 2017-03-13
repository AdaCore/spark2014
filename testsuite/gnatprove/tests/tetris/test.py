from test_support import *

# test would require CVC4 and Alt-Ergo to prove all
# change script when CVC4 can be run with a step limit

# $ gnatprove -P test.gpr --prover=cvc4 --timeout=5
# tetris.adb:43:24: warning: assertion might fail, requires Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX)
# tetris.adb:73:24: warning: assertion might fail, requires Is_Empty (Cur_Board, Cur_Piece.Y + YY, Cur_Piece.X + XX)
# $ gnatprove -P test.gpr --timeout=10
# <no unproved checks>

prove_all(prover=["cvc4", "altergo"],steps=3000,procs=0, counterexample=False)
