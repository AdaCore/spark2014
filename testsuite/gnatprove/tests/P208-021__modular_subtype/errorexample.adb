pragma SPARK_Mode;

package body ErrorExample is

   procedure comp
      (Calculated_Force : Unsigned_32_M1_0_M100_0)
   is
   begin
      pragma Assert (False);  --  @ASSERT:FAIL
   end comp;
end ErrorExample;
