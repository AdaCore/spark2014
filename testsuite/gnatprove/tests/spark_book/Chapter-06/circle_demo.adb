with Ada.Text_IO;
with Shapes5;

-- The purpose of this procedure is to explore certain features of SPARK's handling of functions
-- in assertions. Notice here we have assertions that use a function with a global Input item.
-- When line 13 is commented out it seems like the precondition of Inside_Circle should be proved
-- (and it is). When line 13 is active the precondition cannot be proved and, in fact, will fail.
procedure Circle_Demo
  with SPARK_Mode is
   My_Circle : Shapes5.Circle;
begin
   My_Circle := Shapes5.Make_Circle(X => 0, Y => 0, Radius => 5);
   -- Shapes5.Wild_Man := -1;
   if Shapes5.Inside_Circle(X => 0, Y => 0, C => My_Circle) then
      Ada.Text_IO.Put_Line("The origin is inside the circle");
   else
      Ada.Text_IO.Put_Line("The origin is not inside the circle");
   end if;
end Circle_Demo;
