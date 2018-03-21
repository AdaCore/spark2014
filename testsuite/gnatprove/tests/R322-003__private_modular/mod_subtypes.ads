package Mod_Subtypes with SPARK_Mode is
   type My_Mod is private;

private
   type My_Mod is mod 2 ** 8 - 1;

   function Even (X : My_Mod) return Boolean is (X mod 2 = 0);

   subtype My_Sub is My_Mod with Predicate => Even (My_Sub);

   function "+" (X, Y : My_Sub) return My_Sub;

   pragma Import (Intrinsic, "+");

   function Id (X : My_Sub) return My_Sub is (X);

   A : constant My_Sub := Id (2);
   B : constant My_Sub := Id (2 ** 8 - 2);
   C : constant My_Sub := A + B; --@PREDICATE_CHECK:FAIL

end Mod_Subtypes;
