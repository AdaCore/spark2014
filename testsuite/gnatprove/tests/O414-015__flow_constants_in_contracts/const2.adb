package body Const2
  with Refined_State => (State => V2)  --  Missing C
is

   function Get_V return Integer is (V);

   C : constant Integer := Get_V;

   V2 : Integer := 10;

   procedure Increase (X : in out Integer) is
   begin
      X := X + C;
   end Increase;

end Const2;
