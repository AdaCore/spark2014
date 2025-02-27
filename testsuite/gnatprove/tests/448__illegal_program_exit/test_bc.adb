procedure Test_BC with SPARK_Mode is
   type Int_Access is access Integer;
   type Gen_Int_Access is access all Integer;
   G1 : Int_Access;
   G2 : aliased Integer;

   --  Check that objects mentioned in the exit post are readable (neither
   --  moved not borrowed) when the program is exited.

   procedure P1 with
     Import,
     Always_Terminates,
     Global => null,
     Program_Exit => True;

   procedure Call_P1_Moved with
     Global => (In_Out => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0
   is
      X : Int_Access := G1;
   begin
      P1; --  check: G1 might be moved
      G1 := X;
   end Call_P1_Moved;

   procedure Call_P1_Borrowed with
     Global => (In_Out => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0
   is
      X : access Integer := G1;
   begin
      P1; --  check: G1 might be borrowed
   end Call_P1_Borrowed;

   procedure Call_P1_Observed with
     Global => (In_Out => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0
   is
      X : access constant Integer := G1;
   begin
      P1; --  ok
   end Call_P1_Observed;
   --
   procedure Call_P1_Shallow_Moved with
     Global => (In_Out => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0
   is
      X : Gen_Int_Access := G2'Access;
   begin
      P1; --  check: G2 might be moved
   end Call_P1_Shallow_Moved;

   procedure Call_P1_Shallow_Borrowed with
     Program_Exit => G1 /= null and G2 /= 0
   is
      X : access Integer := G2'Access;
   begin
      P1; --  check: G2 might be borrowed
   end Call_P1_Shallow_Borrowed;

   procedure P2 with
     Import,
     Always_Terminates,
     Global => (Output => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0;

   procedure Call_P2 with
     Global => (In_Out => (G1, G2)),
     Program_Exit => G1 /= null and G2 /= 0
   is
   begin
      P2;
   end Call_P2;
begin
   null;
end;
