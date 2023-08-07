procedure T1 with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
      W : R;
   begin
      return True;
   end F;

   V : R;
begin
   null;
end;
