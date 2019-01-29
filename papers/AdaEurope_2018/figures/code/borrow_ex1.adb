with Ada.Text_IO;
use Ada.Text_IO;



procedure borrow_ex1 with SPARK_Mode is

type Int_Ptr is access Integer;

procedure Swap_Contents (X_Param, Y_Param : in Int_Ptr) is
  Tmp : integer := X_Param.all;
begin
  X_Param.all := Y_Param.all;
  Y_Param.all := Tmp;
end Swap_Contents;

X : Int_Ptr := new Integer'(13);
Y : Int_Ptr := new Integer'(17);

Swap_Contents(X, Y);
	(...)
end borrow_ex1;


