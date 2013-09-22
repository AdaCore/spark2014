package body Foo
is

   procedure Floats_And_Double (X : Float; Y : Long_Float)
   is
   begin
      pragma Assert ((Float (Y) = X) = (Long_Float (X) = Y));
   end Floats_And_Double;

end Foo;
