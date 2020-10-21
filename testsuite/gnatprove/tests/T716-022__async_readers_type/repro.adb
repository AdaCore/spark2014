package body Repro
is
   procedure Foo (Value : in     Volatile_Type;
                  I     :    out Natural)
   is
   begin
      I := Value.I;
      pragma Assert (I = Value.I);
   end Foo;

   procedure Bar (Value : in out Volatile_Type)
   is
   begin
      Value.I := 5;
   end Bar;
end Repro;
