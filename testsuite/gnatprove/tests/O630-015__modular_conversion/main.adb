with Interfaces;
with Foo;

procedure Main
with
    SPARK_Mode,
    Global => (Output => Foo.State)
is
   use type Interfaces.Unsigned_32;

   Value : Interfaces.Unsigned_32;
begin
   Foo.Init;
   Foo.Get (Field => 3,
            Data  => Interfaces.Unsigned_64 (Value)); --@RANGE_CHECK:FAIL

   if Value /= 0 then
      Foo.Init;
   end if;
end Main;
