with P; use P;
procedure Main is
   procedure Sub is
   begin
      pragma Assert (E);
      pragma Assert (M);
   end Sub;
begin
   pragma Assert (C);
   pragma Assert (D);
   pragma Assert (F);
   Sub;
end Main;
