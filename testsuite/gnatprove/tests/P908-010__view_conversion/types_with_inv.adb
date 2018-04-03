package body Types_With_Inv with SPARK_Mode is

   procedure Set_To_Zero (X : out T1) is
   begin
      X := 0;
   end Set_To_Zero;

   procedure Test (X : in out T2) is
   begin
      Set_To_Zero (T1 (X));
   end Test;

   procedure Test2 (X : in out T2) is
   begin
      Set_To_Zero (X);
   end Test2;

   procedure Set_To_Zero (X : out R1) is
   begin
      X.F := 0;
   end Set_To_Zero;

   procedure Test (X : in out R2) is
   begin
      Set_To_Zero (R1 (X));
   end Test;

   procedure Test2 (X : in out R2) is
   begin
      Set_To_Zero (X);
   end Test2;
end Types_With_Inv;
