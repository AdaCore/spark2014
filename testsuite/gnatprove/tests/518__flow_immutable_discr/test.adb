procedure Test with SPARK_Mode is

   type Set (Capacity : Natural) is record
      Length : Natural;
   end record;

   procedure P_1 (S : in out Set) is
      C : Natural range 0 .. S.Capacity := 0;
   begin
      null;
   end P_1;

   procedure P_2 (Capacity : Natural) is
      C : Natural range 0 .. Capacity := 0;
   begin
      null;
   end P_2;

begin
   null;
end Test;
