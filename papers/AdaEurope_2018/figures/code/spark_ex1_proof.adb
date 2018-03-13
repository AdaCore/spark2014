with Ada.Text_IO;
use Ada.Text_IO;



procedure spark_ex1 with SPARK_Mode is
  type Int_Ptr is access integer;

procedure Swap_Contents(X_Param, Y_Param : in Int_Ptr) with
  Post => X_Param.all = Y_Param.all'Old
	and Y_Param.all = X_Param.all'Old;
is
  Tmp : Integer := X_Param.all;
begin
  X_Param.all := 0;
  X_Param.all := Y_Param.all;
  Y_Param.all := Tmp;
end Swap_Contents;

procedure Add_One(X_Param, Y_Param : in Int_Ptr) with
  Post => X_Param.all = X_Param.all'Old + 1
	and Y_Param.all = Y_Param.all'Old + 1;
is
  X_Param.all := X_Param.all + 1;
  Y_Param.all := Y_Param.all + 1;
end Add_One;

  X : Int_Ptr := new Integer'(1);
  (...)

  Add_One (X, X);
  pragma Assert (X.all = 2);  --  incorrect assertion

  Swap_Contents (X, X);
  pragma Assert (X.all = 1);  --  incorrect assertion

begin
  Swap(X, Y);
  (...)
end spark_ex1;
