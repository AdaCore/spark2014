package Pack is

   type Dollar_Amount  is new Float;

   subtype Interest_Rate is Dollar_Amount digits 4;

   type Fraction is delta 2.0**(-15) range -1.0 .. 1.0 - 2.0**(-15);

   subtype Fraction2 is Fraction delta 2.0**(-15);
end Pack;
