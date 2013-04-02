procedure Foo
is
   generic
      type I is range <>;
   procedure Wibble (A, B : in out I);

   procedure Wibble (A, B : in out I)
   is
   begin
      if A / B > 0 then
         A := B;
      else
         B := A;
      end if;
   end Wibble;

   X, Y : Integer := 0;

   procedure Bar is new Wibble (I => Integer);
begin
   Bar (X, Y);
end Foo;
