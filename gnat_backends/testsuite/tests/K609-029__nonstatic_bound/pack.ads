package Pack is

   type Numerals is range -256 .. 255;

   Min : Numerals  := Numerals'First;

   subtype Numerals_Nonstatic is Numerals  range Min .. 255;

end Pack;
