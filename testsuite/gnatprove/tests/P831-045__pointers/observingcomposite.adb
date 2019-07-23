with Ada.Text_IO;
use Ada.Text_IO;



procedure observingcomposite with SPARK_Mode is

  type Int_Ptr is access integer;
  type Rec is record
	X, Y : Int_Ptr;
  end record;

  function Sum (X, Y : access Integer) return Integer is (X.all + Y.all);
  
  function Sum_Rec (R : in Rec) return Integer is
  begin
	return Sum (R.X, R.Y);
  end Sum_Rec;

  XR1 : Int_Ptr := new Integer;
  YR1 : Int_Ptr := new Integer;
  R1 : Rec := (XR1, YR1);
  Y : Integer := Sum_Rec (R1);
  begin
	Y := Sum_Rec (R1);
	--  (...);
  end observingcomposite;




