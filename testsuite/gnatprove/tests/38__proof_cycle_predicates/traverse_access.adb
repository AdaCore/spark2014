procedure Traverse_Access with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   subtype S is R with Predicate => True;

   type S_Acc is access S;

   type Holder is record A : S_Acc; end record;

   function F (V : T) return Boolean
   is
     R : Holder;
   begin
     return True;
   end F;

begin
   null;
end;
