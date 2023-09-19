procedure Membership_Test with SPARK_Mode is
   type T is record A : Integer; end record;

   function Foo (V : T) return Boolean with Pre => True, Post => False;

   function Bar (V : T) return Boolean is (True);

   subtype R is T with Predicate => Foo (R);

   subtype S is R with Predicate => Bar (S);

   function Foo (V : T) return Boolean is (V in S);

begin
   null;
end;
