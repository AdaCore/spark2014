package body Simple_OO_With_Contracts is
   procedure Do_Stuff (Par : T) is
   begin
      pragma Assert (G1 = G2);
      G3 := G3 + G2;
      G4 := Par.X + G3;
   end Do_Stuff;

   overriding
   procedure Do_Stuff (Par : T1) is
   begin
      pragma Assert (G1 = G2);
      G3 := G3 + Par.X + Par.Y;
   end Do_Stuff;

   overriding
   procedure Do_Stuff (Par : T2) is
   begin
      pragma Assert (G3 = Par.Z1);
      G4 := 0;
   end Do_Stuff;

   overriding
   procedure Do_Stuff (Par : T3) is
   begin
      for I in 1 .. G3 loop
         pragma Assert (G2 /= I + Par.Z2);
      end loop;
   end Do_Stuff;
end Simple_OO_With_Contracts;
