package body Bar
is

   G1 : Integer := 0;
   G2 : Integer := 0;
   B  : Boolean := True;

   function Wobble return Boolean;

   function Wobble
     return Boolean
   is
   begin
      return B;
   end Wobble;


   function Wibble (X : Integer;
                    Y : Integer)
                    return Boolean
   is
   begin
      pragma Assert (Y = G2);
      return X = G1 + G2;
   end Wibble;

   function Donk (X : Integer) return Boolean is (X = G1);

   procedure Flip
     with Pre  => True,
          Post => True;

   procedure Flip
   is
   begin
      B := not B;
   end Flip;

   procedure Flop (X : Boolean;
                   Y : Boolean);

   procedure Flop (X, Y: Boolean)
   is
   begin
      B := not X and then not Y;
      G2 := G1;
   end Flop;

end Bar;
