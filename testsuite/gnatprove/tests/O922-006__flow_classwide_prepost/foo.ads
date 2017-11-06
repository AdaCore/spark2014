package Foo is pragma Elaborate_Body;

   type Point is tagged record
      X : Integer;
      Y : Integer;
   end record;

   Limit : Integer := 666;

   procedure Wibble (P : in out Point)
   with Global     => (Proof_In => Limit),
        Pre'Class  => P.X <= Limit,
        Post'Class => P.X = P.Y;

   type Blinking_Point is new Point with record
      Annoyance_Level : Positive;
   end record;

   procedure Wibble (P : in out Blinking_Point);

end Foo;
