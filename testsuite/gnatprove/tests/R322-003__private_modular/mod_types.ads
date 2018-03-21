package Mod_Types with SPARK_Mode is
   type My_Mod is private;

   A : constant My_Mod;
   B : constant My_Mod;
   C : constant My_Mod;

   function "+" (X, Y : My_Mod) return My_Mod;

private
   type My_Mod is mod 2 ** 8 - 1;

   pragma Import (Intrinsic, "+");

   function Id (X : My_Mod) return My_Mod is (X);

   A : constant My_Mod := Id (2);
   B : constant My_Mod := Id (2 ** 8 - 2);
   C : constant My_Mod := Id (0);

   pragma Assert (A + B = C); --@ASSERT:FAIL
end Mod_Types;
