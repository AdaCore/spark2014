with Ada.Text_IO;
use Ada.Text_IO;



procedure observe_ex11 with SPARK_Mode is

  type Int_Ptr is access Integer;


function Sum (X_Param, Y_Param : access constant Integer) return Integer is
  begin
    return X_Param.all + Y_Param.all;
  end Sum;


  X : Int_Ptr := new Integer;
  Y : Integer;

  Begin
	Y := Sum (X, X);
  End observe_ex11;


