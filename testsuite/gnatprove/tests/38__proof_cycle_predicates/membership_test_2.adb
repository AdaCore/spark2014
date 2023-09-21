procedure Membership_Test_2 with SPARK_Mode is
   type T is record A : Integer; end record;

   function Foo (V : T) return Boolean with Pre => True, Post => False;

   function Bar (V : T) return Boolean is (True);

   subtype R is T with Predicate => Foo (R);

   subtype S is R with Predicate => Bar (S);

   subtype U is T;

   function Foo (V : T) return Boolean is (V in U | S);

begin
   null;
end;
