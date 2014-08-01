package body C330002_0 with SPARK_Mode is

   procedure Assign_Array (A : out Array_Type) is
   begin
      A := (84, 36); -- @LENGTH_CHECK:FAIL
   end Assign_Array;

   procedure Assign_Array_Post (A : out Array_Type) is
   begin
      A := (85, 36); -- @LENGTH_CHECK:FAIL
   end Assign_Array_Post;

end C330002_0;
