procedure Main is
   B : Boolean;

   procedure Sub (X : out Boolean)
     with Post => X;

   procedure Sub (X : out Boolean) is separate;

   procedure Sub2 (X : out Boolean) is separate;
begin
   Sub (B);
   pragma Assert (B);
   Sub2 (B);
   pragma Assert (not B);
end;
