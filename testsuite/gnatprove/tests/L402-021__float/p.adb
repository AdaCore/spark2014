procedure P (X : Float) is
   C : Float := Float'Ceiling (X);
   F : Float := Float'Floor (X);
   R : Float := Float'Rounding (X);
   T : Float := Float'Truncation (X);
begin
   pragma Assert (C >= X);
   pragma Assert (C-1.0 < X); --@ASSERT:FAIL
   pragma Assert (F <= X);
   pragma Assert (F+1.0 > X); --@ASSERT:FAIL
   pragma Assert (R = C or else R = F);
   pragma Assert (T = C or else T = F);
end P;
