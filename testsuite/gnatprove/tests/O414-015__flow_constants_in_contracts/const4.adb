package body Const4
  with Refined_State => (State => (C2, H))  --  Cannot mention C2 here
is
   C2 : constant Integer := 10;
   H  : Integer          := 20;

   function Get_C return Integer is (C);

   procedure P (X : out Integer) is
   begin
      X := C;
   end P;

   procedure P2 is
   begin
      H := 15;
   end P2;
end Const4;
