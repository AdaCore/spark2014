pragma SPARK_Mode;
with Pack; use Pack;

procedure P is
   A : T := 1;
   B : T := 11;
   C : T := -1;
begin
   Pack.Ident (A, B, C);
   Pack.Ident (A, B, C);
end P;
