package body B with Refined_State => (State_A => (G, I))
is

   I : Boolean;

   procedure P1 with Refined_Global => (Output => (G, I))
   is
   begin
      P3;
      P8;
   end P1;

   procedure P2 with Refined_Global => (Input  => G,
                                        Output => I)
   is
   begin
      I := G;
   end P2;

   procedure P3 with Refined_Global => (Output => I)
   is
   begin
      I := False;
   end P3;

   procedure P8 with Refined_Global => (Output => G)
   is
   begin
      G := False;
   end P8;

end B;
