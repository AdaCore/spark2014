procedure Aliasing_Check_Array with SPARK_Mode is
   type Arr is array (Positive range <>) of Integer;
   A : Arr (1 .. 5) := [1, 2, 3, 4, 5];

   procedure Swap (I, J : in out Integer) with Import;
   function Id (I : Integer) return Integer is (I) with Pre => True;
begin
   Swap (A (Id (1)), A (3));
end Aliasing_Check_Array;
