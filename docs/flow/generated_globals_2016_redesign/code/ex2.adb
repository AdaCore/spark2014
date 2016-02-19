package body Ex2 with
   Refined_State =>
     (State => (G0, G1, G2, Q.Nested))
is
   G0 : Boolean := False;
   G1 : Boolean := False;
   G2 : Boolean := False;

   package Q with
      Abstract_State => Nested
   is
      procedure P1 with
         Global => (Input  => G1,
                    In_Out => G2,
                    Output => (G0, Nested));

      procedure P4 with
         Global => (Input  => (G1, G2),
                    Output => Nested);

      procedure P5 with
         Global => (Input  => (G1, G2),
                    Output => Nested);
   end Q;

   package body Q with
      Refined_State =>
        (Nested => (G3, G4))
   is
      G3 : Boolean := False;
      G4 : Boolean := False;

      procedure P1 with
         Refined_Global => (Input  => G1,
                            In_Out => G2,
                            Output => (G0, G3, G4))
      is begin
         P2;
         G3 := False;
      end P1;

      procedure P4 with
         Refined_Global => (Input  => (G1, G2),
                            Output => (G3, G4))
      is begin
         P5;
         G3 := not G3;
      end P4;

      procedure P5 with
         Refined_Global => (Input  => (G1, G2),
                            Output => (G3, G4))
      is begin
         G3 := G1;
         G4 := G2;
      end P5;
   end Q;

   procedure P0 with
      Refined_Global => (In_Out => (G1, G2),
                         Output => (G0, Q.Nested))
   is begin
      Q.P1;
      G1 := False;
   end P0;

   procedure P2 with
      Refined_Global => (Input  => G1,
                         In_Out => G2,
                         Output => (G0, Q.Nested))
   is begin
      P3;
      G0 := False;
      G2 := False;
   end P2;

   procedure P3 with
      Refined_Global => (Input  => (G1, G2),
                         Output => Q.Nested)
   is begin
      Q.P4;
   end P3;
end Ex2;
