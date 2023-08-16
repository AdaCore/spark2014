procedure Imported_2 with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post =>  False;

   subtype R is T with Predicate => F (R);

   procedure Imp (A : Integer; X : R) with Import;

   function F (V : T) return Boolean
   is
   begin
      Imp (1, V);
      return True;
   end F;

begin
   null;
end;
