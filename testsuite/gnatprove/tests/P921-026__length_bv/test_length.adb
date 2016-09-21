with BV_Arrays; use BV_Arrays;
procedure Test_Length with SPARK_Mode is

   procedure P1 with Pre => True is
      A : My_Array := Create (Mod_16'Last);

      C : Short_Short_Integer := A'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end P1;

   procedure P2 with Pre => True is
      A1 : My_Array := Create (Mod_16'Last);

      C1 : Mod_16 := A1'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end P2;

   procedure P3 with Pre => True is
      A2 : My_Array := Create (Mod_16'Last - 3);

      C2 : Mod_8 := A2'Length; --@RANGE_CHECK:FAIL
   begin
      null;
   end P3;

begin
   P1;
   P2;
   P3;
end Test_Length;
