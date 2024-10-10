procedure P (Cond : Boolean)
  with Global => null
is
   function F (X : Integer) return Boolean with Global => (Input => Cond);

   subtype Natural_Int is Integer with Predicate => F (Natural_Int);
   subtype Positive_Int is Natural_Int with Predicate => Positive_Int > 0;

   function F (X : Integer) return Boolean is
   begin
      return Cond and X >= 0;
   end;

   function Is_Positive (X : Integer) return Boolean is (X in Positive_Int)
   with Global => null;
begin
   null;
end;
