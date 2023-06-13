package body Pack is

   procedure Skip_Entirely is
   begin
      X := F;
      pragma Assert (X);
   end Skip_Entirely;

   procedure Skip_Proof is
   begin
      X := F;
      pragma Assert (X);
   end Skip_Proof;

   procedure Process_Normally is
   begin
      X := F;
      pragma Assert (X);
   end Process_Normally;

end Pack;
