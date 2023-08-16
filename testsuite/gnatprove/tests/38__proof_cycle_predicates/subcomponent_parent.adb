procedure Subcomponent_Parent with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   subtype S is R with Predicate => True;

   type Rec is record V : S; end record;

   type Holder is record R : Rec; end record;

   function F (V : T) return Boolean
   is
     R : Holder;
   begin
     return True;
   end F;

begin
   null;
end;
