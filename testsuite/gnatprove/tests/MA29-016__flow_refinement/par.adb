with Par.Pub;
with Par.Priv;
with Par.Priv2;

package body Par
  with Refined_State => (State => (Z,
                                   Y,
                                   Priv.D,
                                   Priv.Private_Child_State,
                                   Priv2.D2,
                                   Priv2.More_Private_State))
is

   Z : Integer;

   function Wibble return Integer
--   with Refined_Global => (X, Y, Z)
   is
   begin
      return X + Y + Z;
   end Wibble;

   procedure Stuff
   is
   begin
      Z := X + Y;
   end Stuff;

   procedure Test_1
   is
   begin
      Z := Par.Pub.F;
      --  par.pub|spec is visible
      --  par.pub|priv is not
   end Test_1;

   procedure Test_2
   is
   begin
      Z := Par.Priv.D;
      --  par.priv|spec is visible
      --  par.priv|priv is not
   end Test_2;

end Par;
