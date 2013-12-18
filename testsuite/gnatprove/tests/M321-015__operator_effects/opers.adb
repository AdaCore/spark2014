package body Opers is

   function Apply_To_Self (X : T) return T is
   begin
      return X + X;
   end Apply_To_Self;

   function Double1 is new Apply_To_Self (Integer);

   function Double2 is new Apply_To_Self (Integer, "+");

   function Ten1 is new Apply_To_Self (My_Int);

   function Ten2 is new Apply_To_Self (My_Int, "+");

   function Compare_With_Self (X : T) return Boolean is
   begin
      return X < X;
   end Compare_With_Self;

   function False1 is new Compare_With_Self (Integer);

   function False2 is new Compare_With_Self (Integer, "<");

   function Fixed_True1 is new Compare_With_Self (My_Int);

   function Fixed_True2 is new Compare_With_Self (My_Int, "<");

   function Equal_With_Self (X : T) return Boolean is
   begin
      return X = X;
   end Equal_With_Self;

   function True1 is new Equal_With_Self (Integer);

   function True2 is new Equal_With_Self (Integer, "=");

   function Fixed_False1 is new Equal_With_Self (My_Int);

   function Fixed_False2 is new Equal_With_Self (My_Int, "=");

end Opers;
