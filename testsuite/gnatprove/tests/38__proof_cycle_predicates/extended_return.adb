procedure Extended_Return with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
   begin
      return X : Boolean do
         X := (R (V).A = 1);
      end return;
   end F;

begin
   null;
end;
