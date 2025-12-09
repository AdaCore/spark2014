with Ada.Unchecked_Conversion;

procedure P with SPARK_Mode is

   type R_1 is record
      F, G : Integer;
   end record;

   function F_Id_1 is new Ada.Unchecked_Conversion (R_1, R_1);

   type R_2 is record
      F, G : Natural;
   end record;

   function F_Id_2 is new Ada.Unchecked_Conversion (R_2, R_2) with Potentially_Invalid;

   procedure Test_1 (X : R_1) is
   begin
      pragma Assert (F_Id_1 (X) = X);
   end Test_1;

   procedure Test_2 (X : R_2) is
   begin
      pragma Assert (F_Id_2 (X) = X);
   end Test_2;

begin
   null;
end P;
