package Outer
  with Abstract_State => A2
is
   procedure Init_A2
     with Global => (Output => A2);

private
   --  A variable declared in the private part must have a Part_Of aspect
   Private_State : Integer
     with Part_Of => A2;
end Outer;
