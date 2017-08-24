package body Foo is

   function Invariant (A : Level_1;
                       B : Level_1;
                       C : Level_1)
                       return Boolean
   is (A.B1.A1 and B.B2.A2 and C.B3.A3)
   with Global => null;

   procedure Init_R (X : Integer)
   with Global => (Output => Red)
   is
   begin
      Red := (others => (others => (others => X >= 0)));
   end Init_R;

   procedure Init_B (X : Integer)
   with Global => (Output => Black)
   is
   begin
      Black := (others => (others => (others => X >= 0)));
   end Init_B;

   procedure Initialise (X : Integer)
   is
   begin
      Init_R (X);
      pragma Assert (Invariant (A => Red.C1,
                                B => Red.C2,
                                C => Red.C3));
      Init_B (X);
      pragma Assert (Invariant (A => Black.C1,
                                B => Black.C2,
                                C => Black.C3));
      pragma Assert (Invariant (A => Red.C1,
                                B => Red.C2,
                                C => Red.C3) and then
                     Invariant (A => Black.C1,
                                B => Black.C2,
                                C => Black.C3));
   end Initialise;

end Foo;
