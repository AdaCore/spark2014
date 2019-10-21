procedure F
  (X1, X2 : Integer;
   Y1, Y2 : out Integer)
with Depends => (Y1 => X1, Y2 => X2),
     Post => Y1 = X1 and Y2 = X2
is
   type T (D : Integer) is null record;

   type R is record
      C1 : T (X1);
      C2 : T (X2);
   end record;

   A : R;
   B1 : T := A.C1;
   B2 : T := A.C2;
begin
   Y1 := B1.D;
   Y2 := B2.D;
end;
