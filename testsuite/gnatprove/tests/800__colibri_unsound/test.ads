with SPARK.Big_Integers;

package Test
with
  Elaborate_Body,
  Ghost
is

   type Word32 is mod 2 ** 32;

   subtype Univ_Int is SPARK.Big_Integers.Big_Integer;
   use type Univ_Int;

   package Word32_Conversion is
     new SPARK.Big_Integers.Unsigned_Conversions (Int => Word32);

   function Int_Of (W : Word32) return Univ_Int
     renames Word32_Conversion.To_Big_Integer;

   function Ident (M : Univ_Int) return Univ_Int;

   procedure Test
     (MI  : Univ_Int)
   with
     Pre => MI /= 0,
     Post => False;

end Test;
