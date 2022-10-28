procedure Main is
   generic
     with procedure P is null with Pre => False;
   procedure G;

   procedure G is
   begin
      P;
   end;

   procedure I is new G;
begin
   I;
end;
