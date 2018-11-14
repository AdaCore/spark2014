package body A.Child with Refined_State => (State_B => (H, J))
is

   J : Boolean;

   procedure P4
   is
   begin
      G := False;
   end P4;

   procedure P5
   is
   begin
      P3;
      P4;
   end P5;

   procedure P6
   is
   begin
      H := G;
      J := G;
   end P6;

   procedure P7
   is
   begin
      P3;
      P5;
   end P7;

end A.Child;
