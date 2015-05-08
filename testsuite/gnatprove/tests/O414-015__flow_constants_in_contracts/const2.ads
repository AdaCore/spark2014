package Const2
  with Abstract_State => State
  --       Initializes    => (V, State)
is
   V : Integer := 0;

   function Get_V return Integer
     with Pre => True;

   procedure Increase (X : in out Integer)
     with Pre => True;

end Const2;
