procedure Main with SPARK_Mode is
   type My_Mod is mod 31;
   F : Natural := 32;
   G : My_Mod'Base := My_Mod'Mod (F);
begin
   pragma Assert (G = 0); --@ASSERT:FAIL
end Main;
