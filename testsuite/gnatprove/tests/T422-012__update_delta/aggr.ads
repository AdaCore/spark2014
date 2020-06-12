package Aggr with SPARK_Mode is

   type Rec is record
      X : Integer;
      Y : Positive;
   end record;

   function Create (Z : Integer) return Rec is
      (Rec'(X | Y => Z)); --@RANGE_CHECK:FAIL

   function Up (R : Rec; Z : Integer) return Rec is
      (R'Update (X | Y => Z)); --@RANGE_CHECK:FAIL

   function Del (R : Rec; Z : Integer) return Rec is
      ((R with delta X | Y => Z)); --@RANGE_CHECK:FAIL

end Aggr;
