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

   procedure Test (A : in out Integer) is
   begin
      A := Double1 (A);
      A := Double2 (A);
      A := Integer (Ten1 (My_Int (A)));
      A := Integer (Ten2 (My_Int (A)));
      pragma Assert (not False1 (A));
      pragma Assert (not False2 (A));
      pragma Assert (Fixed_False1 (My_Int (A)));
      pragma Assert (Fixed_False2 (My_Int (A)));
      pragma Assert (True1 (A));
      pragma Assert (True2 (A));
      pragma Assert (not Fixed_True1 (My_Int (A)));
      pragma Assert (not Fixed_True2 (My_Int (A)));
   end Test;

end Opers;
