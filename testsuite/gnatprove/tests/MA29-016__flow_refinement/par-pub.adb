with Par.Priv;

package body Par.Pub
is

   procedure Stuff
   is
   begin
      A := Par.X + Par.Y;
      -- par|spec is visible
      -- par|priv is visible
   end Stuff;

   procedure Test
   is
   begin
      A := Par.Priv.D;
      -- par.priv|spec is visible
      -- par.priv|priv is not visible
   end Test;


end Par.Pub;
