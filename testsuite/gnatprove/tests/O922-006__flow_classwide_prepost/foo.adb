package body Foo is

   procedure Wibble (P : in out Point)
   is
   begin
      P.X := P.Y;
   end Wibble;

   procedure Wibble (P : in out Blinking_Point)
   is
   begin
      pragma Assert (P.X <= Limit or P.Y <= Limit);
      P.X               := P.Y;
      P.Annoyance_Level := 9001;
   end Wibble;

end Foo;
