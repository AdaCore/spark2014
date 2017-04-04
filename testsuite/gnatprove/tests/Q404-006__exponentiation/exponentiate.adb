with Interfaces; use Interfaces;

function Exponentiate (Val : Unsigned_32; Exp : Natural) return Unsigned_32
  with Post => Exponentiate'Result = Val ** Exp
is
   Cur_Exp : Unsigned_32 := Unsigned_32 (Exp);
   Cur_Val : Unsigned_32 := Val;
   Result  : Unsigned_32 := 1;
   Iter    : Natural range 0 .. 31 := 0 with Ghost;
   function Pow2 (I : Natural) return Unsigned_32 is (2 ** I) with Ghost;
begin
   if Exp = 0 then
      return 1;
   end if;

   while Cur_Exp /= 0 loop
      pragma Loop_Invariant (Result = Val ** Natural(Unsigned_32(Exp) mod (Pow2 (Iter))));
      pragma Loop_Invariant (Cur_Val = Val ** Natural(Pow2 (Iter)));
      pragma Loop_Invariant (Cur_Exp = Cur_Exp'Loop_Entry / (Pow2 (Iter)));
      if Cur_Exp mod 2 = 1 then
         Result := Result * Cur_Val;
      end if;
      Cur_Exp := Cur_Exp / 2;
      Cur_Val := Cur_Val * Cur_Val;
      Iter    := Iter + 1;
   end loop;

   return Result;
end Exponentiate;
