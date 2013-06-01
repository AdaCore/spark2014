
--  model for "type Mod is mod 2;"

private open util/relation
private open util/integer

sig Mod {}

one sig Conversions
{
   integer_of_mod : Mod -> lone Int,
   mod_of_integer : Int -> lone Mod
}
{
   --  This model of Conversion should at least cover the domain of
   --  the modular type
   
   dom[integer_of_mod] = Mod
   ran[mod_of_integer] = Mod

   --  "coerce" axiom
   
   all x : dom[mod_of_integer] {
      ((x.mod_of_integer).integer_of_mod) = rem [x, 2]
   }

   --  "range" axiom
   
   all x : Mod {
      x.integer_of_mod >= 0
      x.integer_of_mod <= 1
   }
}

fact {
   --  Define equality between Mods using equality between Ints
   
   all x1, x2 : Mod {
      x1.(Conversions.integer_of_mod) = x2.(Conversions.integer_of_mod) =>
	 x1 = x2
   }
}

pred show [] {
   --  Show conversions for Int in range 0 .. 4
   
   all x : Int {
      (x >= 0 and x < 5) implies x in dom[Conversions.mod_of_integer]
   }
}

run show for 7 Mod, 5 int
