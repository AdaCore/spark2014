package Frame_Condition with
  SPARK_Mode
is
   type Index is range 1 .. 100;
   type Arr is array (Index) of Integer;

   procedure Update_Arr (A : in out Arr; Idx : Index) with
     Post => A(Idx + 1 .. A'Last) = A(Idx + 1 .. A'Last)'Old;

   type Rec is record
      A : Arr;
      X : Integer;
   end record;

   procedure Update_Rec (R : in out Rec) with
     Post => R.X = R.X'Old;

end Frame_Condition;
