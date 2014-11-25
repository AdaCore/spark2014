package Casper
  with Initializes => (G1, G2, Ghost_G1)
is
   G1, G2 : Integer := 0;

   Ghost_G1 : Integer := 0
     with Ghost;

   procedure Ghost_Proc (Par : out Integer)
     with Ghost,
          Global => (Input    => G1,
                     Proof_In => G2);  --  This is the same as Input => G2

   procedure P (Par : out Integer)
     with Global => (Input    => G1,
                     Proof_In => G2,
                     Output   => Ghost_G1);
end Casper;
