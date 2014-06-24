package body Misc
with Refined_State => (State => (G1, G2))
is

   type Record_T is record
      A : Integer;
      B : Integer;
   end record;

   G1 : Record_T;
   G2 : Boolean;

   procedure Test_01 is
   --  proof in G2
   --  in out G1
   begin
      pragma Assert (G2);
      G1.A := 0;
   end Test_01;

   function Test_02 return Boolean
   --  in G1
   is
   begin
      return G1.A > 0;
   end Test_02;

   procedure Test_03 (N : Integer)
   --  in out G1
   --     out G2
   is
   begin
      G1.A := N;
      G2   := False;
   end Test_03;

   procedure Test_04 (N : Integer)
   --  out G1, G2
   is
   begin
      G1.A := 0;
      G1.B := N;
      G2   := G1.A = G1.B;
   end Test_04;

end Misc;
