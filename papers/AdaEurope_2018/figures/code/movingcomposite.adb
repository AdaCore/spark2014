with Ada.Text_IO;
use Ada.Text_IO;



procedure movingcomposite with SPARK_Mode is

type Int_Ptr is access Integer;
type Rec is record
  X, Y : Int_Ptr;
end record;

R : Rec := (...);
S : Rec := (...);

S := R;
(...)
end movingcomposite;



  --XR : Int_Ptr := new Integer;
  --YR : Int_Ptr := new Integer;
  --XS : Int_Ptr := new Integer;
  --YS : Int_Ptr := new Integer;
