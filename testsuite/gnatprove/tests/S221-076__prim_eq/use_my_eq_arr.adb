with New_Eq; use New_Eq;
procedure Use_My_eq_Arr with SPARK_Mode is
   type My_Array is array (Integer range 1 .. 1) of New_Eq.T;
   W, Z  : My_Array;
begin
   pragma Assume (W = Z);
   pragma Assert (My_prop (W (1), Z (1)));
end Use_My_eq_Arr;
