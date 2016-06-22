with Public_Records; use Public_Records;

package body Private_Records with SPARK_Mode is
   procedure P is
      C : Child;
   begin
      pragma Assert (Root (C).F = 1); --@ASSERT:FAIL
   end P;
end Private_Records;
