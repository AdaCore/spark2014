
--  model for "type Signed is -2 .. 2;"

private open util/relation
private open util/integer

sig Signed {}

one sig Conversions
{
   integer_of_signed : Signed -> lone Int,
   signed_of_integer : Int -> lone Signed
}
{
   --  This model of Conversion should at least cover the domain of
   --  the signed type
   
   dom[integer_of_signed] = Signed
   ran[signed_of_integer] = Signed

   --  "coerce" axiom

   all x : dom[signed_of_integer] {
      ((x.signed_of_integer).integer_of_signed) = x
   }

   --  "range" axiom
   
   all x : Signed {
      x.integer_of_signed >= -2
      x.integer_of_signed <= 2
   }
}

fact {
   --  Define equality between Signeds using equality between Ints
   
   all x1, x2 : Signed {
      x1.(Conversions.integer_of_signed) =
      x2.(Conversions.integer_of_signed) implies
	 x1 = x2
   }
}

pred show [] {
   --  Show conversions for Int in range -2 .. 2

   all x: Int {
      (x >= -2 and x <= 2) implies x in dom[Conversions.signed_of_integer]
   }
}

run show for 7 Signed, 5 int
