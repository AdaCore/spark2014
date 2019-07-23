procedure P (X : in out Integer) is
   G, F : Boolean := False;
   H : Boolean := False;

   procedure Q (X : Boolean) with Pre => G and X is
   begin
      H := not H;
   end;

   function R (X : Boolean) return Boolean with Pre => G and X is
   begin
      return H;
   end;

begin
   loop
      Q (F);
      G := R(True);
      F := R(F);
      H := R(G);
   end loop;
end P;
