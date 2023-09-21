procedure Assertion with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
   begin
      pragma Assert (R (V).A = 1);
      return True;
   end F;

begin
   null;
end;
