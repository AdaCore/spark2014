with Ada.Text_IO;
use Ada.Text_IO;



procedure spark_ex1 with SPARK_Mode is
  type Int_Ptr is access integer;

procedure Swap_Contents(X_Param, Y_Param : in Int_Ptr) with
  post => X_Param.all = Y_Param.all'Old 
	and Y_Param.all = X_Param.all'Old; 
  is
  Tmp : Integer := X_Param.all;
begin
  X_Param.all := 0;
  X_Param.all := Y_Param.all;
  Y_Param.all := Tmp;
end Swap_Contents;

X : Int_Ptr := new Integer'(1);
(...)

Swap_Contents (X, X);
pragma Assert (X.all = 1);  --  wrong assertion 

  
  begin
	Swap(X, Y);
	(...)
  end spark_ex1;

