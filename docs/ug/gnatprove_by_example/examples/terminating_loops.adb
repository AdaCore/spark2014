procedure Terminating_Loops (X : Integer) with
  SPARK_Mode
is
   X_Mod_3 : Natural;
begin
   X_Mod_3 := 0;
   while X - X_Mod_3 >= 3 loop
      X_Mod_3 := X_Mod_3 + 3;
      pragma Loop_Variant (Increases => X_Mod_3);
   end loop;

   X_Mod_3 := 0;
   while X - X_Mod_3 >= 3 loop
      X_Mod_3 := X_Mod_3 + 3;
      pragma Loop_Variant (Decreases => X - X_Mod_3);
   end loop;
end Terminating_Loops;
