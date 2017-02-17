package Slice_Test_3
  with SPARK_Mode => On
is

   type Index is range 1 .. 8;

   type Arr is array (Index) of Integer;

   procedure Slice_Dynamic (A : in out Arr;  I, J, K, L: in Index);

end Slice_Test_3;
