with Par.Pub;

private package Par.Priv
  with Abstract_State => (Private_Child_State with Part_Of => State)
is

   D : Integer with Part_Of => State;

   procedure Stuff;

   function H return Integer is (Par.X + Par.Y);
   --  par|spec is visible
   --  par|priv is visible

   function I return Integer is (Par.Pub.A);
   --  par.pub|spec is visible
   --  par.pub|priv is not visible

private

   E : Integer with Part_Of => Private_Child_State;

end Par.Priv;
