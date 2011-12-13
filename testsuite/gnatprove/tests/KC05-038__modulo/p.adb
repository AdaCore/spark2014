procedure P (X, Y : Integer) is
   type M is mod 16;
   type N is range 0 .. 32;
   subtype S is M;

   U : constant M := M(X);
   V : constant M := M(Y);
   W : constant N := N(U - V);
   XS : constant S := U - V;
   A : constant S := U;
   B : constant S := V;
   ZS : constant N := N(A - B);
begin
   null;
end P;
