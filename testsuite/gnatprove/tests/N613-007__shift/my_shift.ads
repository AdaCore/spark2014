package My_Shift is

   type My_Mod is mod 2 ** 32;

   function Shift_Right (Value : My_Mod; Count : Natural) return My_Mod
      with Import,
      Convention => Intrinsic,
      Global     => null;

   procedure P (Z : in out My_Mod);

end My_Shift;
