with Ada.Text_IO;
use Ada.Text_IO;



procedure move_ex1 with SPARK_Mode is
type Int_Ptr is access Integer;

procedure Swap(X_Param, Y_Param : in out Int_Ptr) is
  Tmp : Int_Ptr := X_Param;
begin
  X_Param := Y_Param;
  Y_Param := Tmp;
end Swap;

X : Int_Ptr := new Integer'(7);
Y : Int_Ptr := new Integer'(11);

Swap(X, Y);
  (...)
end move_ex1;

