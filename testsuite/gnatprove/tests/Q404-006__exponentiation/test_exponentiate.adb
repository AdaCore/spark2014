with Interfaces; use Interfaces;
with Exponentiate;

procedure Test_Exponentiate is
   Val : Unsigned_32 := 12329;
begin
   for Exp in 1 .. 100 loop
      pragma Assert (Exponentiate (Val, Exp) = Val ** Exp);
   end loop;
end Test_Exponentiate;
