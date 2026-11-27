with Interfaces;

procedure Nested_Predicate with SPARK_Mode is
   subtype Byte is Interfaces.Unsigned_8;
   use type Byte;
   type Pair is record
      Low, High : aliased Byte;
   end record;
   subtype Ordered is Pair with
     Dynamic_Predicate => Ordered.Low <= Ordered.High;
   type Holder is record
      Value : Ordered;
   end record;
   P : Holder := (Value => (1, 4));
   View : Byte with Import, Address => P.Value.Low'Address;
begin
   View := 5;
   pragma Assert (P.Value.Low <= P.Value.High);
end Nested_Predicate;
