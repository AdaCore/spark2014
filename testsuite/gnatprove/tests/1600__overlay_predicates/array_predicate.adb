with Interfaces;

procedure Array_Predicate with SPARK_Mode is
   subtype Byte is Interfaces.Unsigned_8;
   use type Byte;
   type Pair is array (1 .. 2) of aliased Byte;
   subtype Ordered is Pair with
     Dynamic_Predicate => Ordered (1) <= Ordered (2);
   P : Ordered := (1, 4);
   View : Byte with Import, Address => P (1)'Address;
begin
   View := 5;
   pragma Assert (P (1) <= P (2));
end Array_Predicate;
