procedure Empty_Multidimensional (Hi : Positive) with SPARK_Mode is
   subtype Outer_Index is Positive range 1 .. Hi;
   type Matrix is array (Outer_Index range <>, Integer range <>) of Integer;
   --  A dynamic first dimension keeps the empty aggregate in the tree,
   --  exposing the invalid predecessor in the second dimension.
   V : constant Matrix := []; --@RANGE_CHECK:FAIL
   pragma Unreferenced (V);
begin
   null;
end Empty_Multidimensional;
