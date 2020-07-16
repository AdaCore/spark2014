package Repro
is
   type Volatile_Type is
   record
      I : Natural;
      J : Natural;
   end record
     with
        Volatile,
        Async_Readers;

   procedure Foo (Value : in     Volatile_Type;
                  I     :    out Natural);

   procedure Bar (Value : in out Volatile_Type)
   with
      Post => Value.J = Value'Old.J;
end Repro;
