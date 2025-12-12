package body Foo
with SPARK_Mode => On
is
   type Bar is record
      A : Integer;
   end record;

   procedure Foo (Self : T)
   is
      B : Bar
        with
          Volatile, No_Caching, Address => Self.Address;
   begin
      B.A := 42;
   end Foo;

end Foo;
