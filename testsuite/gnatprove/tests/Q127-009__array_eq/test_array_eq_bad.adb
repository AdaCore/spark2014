procedure Test_Array_Eq_Bad with SPARK_Mode is
   type My_Rec is record
      F1 : Integer;
      F2 : Integer;
   end record;

   function "=" (X, Y : My_Rec) return Boolean is (X.F1 = Y.F1);

   type My_Array is array (Integer range 1 .. 2) of My_Rec;

   A : My_Array := ((1, 2), (3, 4));
   B : My_Array := ((1, 1), (3, 3));
begin
   pragma Assert (A /= B); --@ASSERT:FAIL
end Test_Array_Eq_Bad;
