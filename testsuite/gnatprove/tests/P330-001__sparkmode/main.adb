with Support;
with Support2;

package body Main with SPARK_Mode is
   procedure P is
      X : Integer := Support.F;
   begin
      pragma Assert (X = 1); --@ASSERT:PASS
   end P;

   procedure Q is
      X : Integer := Support2.F;
   begin
      pragma Assert (X = 1); --@ASSERT:PASS
   end Q;
end Main;
