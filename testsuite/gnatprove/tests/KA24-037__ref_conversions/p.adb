with Pack;

procedure P is
   subtype TT is Integer range 1 .. 10;
   subtype TTT is Integer range 1 .. 11;

   A : Pack.T := 1;
   B : TT;
   C : TTT;
begin
   Pack.Ident (A, B, C);
   Pack.Ident (A, B, C);
end P;
