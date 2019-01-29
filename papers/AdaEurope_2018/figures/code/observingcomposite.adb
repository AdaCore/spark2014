with Ada.Text_IO;
use Ada.Text_IO;



procedure observingcomposite with SPARK_Mode is

  type Int_Ptr is access Integer;
  type Rec is record
	X, Y : Int_Ptr;
  end record;

function Sum_Rec (R : in Rec) return Integer is
begin
  return Sum (R.X, R.Y);
end Sum_Rec;

R1 : Rec := (...);

Y : Integer := Sum_Rec (R1);
begin
  Y := Sum_Rec (R1);
  (...);
end observingcomposite;



  --XR1 : Int_Ptr := new Integer;
  --YR1 : Int_Ptr := new Integer;
  --R1 : Rec := (XR1, YR1);
