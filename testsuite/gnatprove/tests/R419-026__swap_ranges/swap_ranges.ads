with Types; use Types;

package Swap_Ranges with
     Spark_Mode is

   procedure Swap_Ranges_With_Error (A : in out T_Arr; B : in out T_Arr) with
      Pre  => A'Length = B'Length,
      Post => A'Old = B and then B'Old = A; --@POSTCONDITION:FAIL

   procedure Swap_Ranges_Without_Error
     (A : in out T_Arr;
      B : in out T_Arr) with
      Pre  => A'Length = B'Length,
      Post => A'Old = B and then B'Old = A;
end Swap_Ranges;
