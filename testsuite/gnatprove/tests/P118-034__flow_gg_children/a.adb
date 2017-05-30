package body A with Refined_State => (State_A => (G, I))
is

   I : Boolean;

   procedure P1
   is
   begin
      P3;
      P8;
   end P1;

   procedure P2
   is
   begin
      I := G;
   end P2;

   procedure P3
   is
   begin
      I := False;
   end P3;

   procedure P8
   is
   begin
      G := False;
   end P8;

end A;
