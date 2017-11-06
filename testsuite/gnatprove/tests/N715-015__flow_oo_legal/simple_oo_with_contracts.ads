package Simple_OO_With_Contracts is pragma Elaborate_Body;
   G1, G2, G3, G4 : Integer := 0;

   type T is tagged record
      X : Integer;
   end record;

   procedure Do_Stuff (Par : T)
     with Global => (Proof_In => G1,
                     Input    => G2,
                     In_Out   => G3,
                     Output   => G4);

   type T1 is new T with record
      Y : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T1)
     with Global => (Proof_In => (G1, G2),
                     Input    => G3,
                     Output   => G4);

   type T2 is new T1 with record
      Z1 : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T2)
     with Global => (Proof_In => G3,
                     Output   => G4);

   type T3 is new T1 with record
      Z2 : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T3)
     with Global => (Proof_In => G2,
                     Input    => G3);
end Simple_OO_With_Contracts;
