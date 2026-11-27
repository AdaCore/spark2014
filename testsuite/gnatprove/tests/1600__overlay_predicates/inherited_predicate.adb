with Interfaces;

procedure Inherited_Predicate with SPARK_Mode is
   subtype Byte is Interfaces.Unsigned_8;
   use type Byte;
   type Pair is record
      Low, High : aliased Byte;
   end record;
   subtype Ordered is Pair with
     Dynamic_Predicate => Ordered.Low <= Ordered.High;
   type Derived is new Ordered;
   P : Derived := (1, 4);
   View : Byte with Import, Address => P.Low'Address;
begin
   View := 5;
   pragma Assert (P.Low <= P.High);
end Inherited_Predicate;
