procedure Main is

   procedure Foo (X : Integer) is
   begin
      null;
   end Foo;

   X : Integer := 0;

   procedure Bar (J : Integer) with Global => null is
   begin
      for I in 1 .. 0 loop
         Foo (J);
      end loop;
   end Bar;

begin
   Bar (X);
end Main;
