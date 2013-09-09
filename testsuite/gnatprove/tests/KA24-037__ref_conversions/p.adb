with Pack;

procedure P (Havok_A, Havok_B : Integer)
with Pre => Havok_A in 1 .. 10 and
            Havok_B in 1 .. 11
is
   subtype TT is Integer range 1 .. 10;
   subtype TTT is Integer range 1 .. 11;

   A : Pack.T := 1;
   B : TT     := Havok_A;
   C : TTT    := Havok_B;
begin
   Pack.Ident (A, B, C);
   Pack.Ident (A, B, C);
end P;
