package Casper
  with Initializes => (G1, G2, Ghost_G1,
                       Nested_Ghost_Package.Nested_Global,
                       Nested_Ghost_Package.Nested_State)
is
   G1, G2 : Integer := 0;

   Ghost_G1 : Integer := 0
     with Ghost;

   procedure Ghost_Proc (Par : out Integer)
     with Ghost,
          Global => (Input    => G1,
                     Proof_In => G2);  --  This is not the same as Input => G2

   procedure P (Par : out Integer)
     with Global => (Input    => (G1, G2),

                     Output   => Ghost_G1);

   package Nested_Ghost_Package
     with Ghost,
          Abstract_State => Nested_State,
          Initializes    => (Nested_Global, Nested_State)
   is
      Nested_Global : Integer := 0;

      function Is_OK (Par : Integer) return Boolean
        with Global => Nested_State;
   end Nested_Ghost_Package;
end Casper;
