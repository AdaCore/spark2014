procedure Main is  
   B : Boolean;

   procedure Sub0 (X : out Boolean)
     with Post => X;

   procedure Sub0 (X : out Boolean) is
   begin
      X := True;
   end;

   procedure Sub (X : out Boolean)
     with Post => X;

   procedure Sub (X : out Boolean) is separate;

   procedure Sub2 (X : out Boolean) is separate;

   package P is
      procedure Sub3 (X : out Boolean)
        with Post => X;
   end P;

   package body P is separate;
begin
   Sub0 (B);
   pragma Assert (B);
   Sub (B);
   pragma Assert (B);
   Sub2 (B);
   pragma Assert (not B);
   P.Sub3 (B);
   pragma Assert (B);
end;
