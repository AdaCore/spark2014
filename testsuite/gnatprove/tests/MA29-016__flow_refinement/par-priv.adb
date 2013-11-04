package body Par.Priv
  with Refined_State => (Private_Child_State => E)
is

   procedure Stuff
   is
   begin
      E := Par.X + Par.Y;
      --  par|spec is visible
      --  par|priv is visible
   end Stuff;

   procedure Test
   is
   begin
      D := Par.Pub.A;
      --  par.pub|spec is visible
      --  par.pub|priv is not visible
   end Test;

end Par.Priv;
