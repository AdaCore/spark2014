with Ada.Text_IO;
use Ada.Text_IO;



procedure borrow_ex1 with SPARK_Mode is

  type Int_Ptr is access integer;

Procedure Swap_Contents (X_Param, Y_Param : in Int_Ptr) is
  Tmp : integer := X_Param.all;
  Begin
    X_Param.all := Y_Param.all;
    Y_Param.all := Tmp;
  End Swap_Contents;

  X : Int_Ptr := new Integer;
  Y : Int_Ptr := new Integer;

  Swap_Contents(X, Y);
	(...)
  end borrow_ex1;
	

