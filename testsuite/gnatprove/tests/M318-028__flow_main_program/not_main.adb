package body Not_Main

is
   X, Y : Integer;

   function Add return Integer
      with Global => (X, Y)
   is
   begin
      return X + Y;
   end Add;

   procedure Double
      with Global => (In_Out => (X, Y))
   is
   begin
      X := X + X;
      Y := 2 * Y;
   end Double;

   function Are_Equal return Boolean is
      (X = Y)
      with Global => (X, Y);

   package Nested
   is
      procedure Do_Nothing;
   end Nested;

   package body Nested
   is
      procedure Do_Nothing
      is
      begin
         null;
      end Do_Nothing;
   end Nested;
end Not_Main;
