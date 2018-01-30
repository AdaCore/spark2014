with Ada.Text_IO;
use Ada.Text_IO;



procedure observe_ex1 with SPARK_Mode is

type Int_Ptr is access integer;

function Sum (X_Param, Y_Param : access constant Integer) return
	Integer is
begin
  return X_Param.all + Y_Param.all;
end Sum;

X : Int_Ptr := new Integer;
Y : Integer;

Y := Sum (X, X);
	(...)
end observe_ex1;


