with Ada.Text_IO;
use Ada.Text_IO;



procedure move_ex1 with SPARK_Mode is
  type Int_Ptr is access integer;

procedure Swap(X_Param, Y_Param : in out Int_Ptr) is
  Tmp : Int_Ptr := X_Param;
begin
  X_Param := Y_Param;
  Y_Param := Tmp;
end Swap;

  X : Int_Ptr := new Integer;
  Y : Int_Ptr := new Integer;
  
  Swap(X, Y);
  (...)
end move_ex1;

