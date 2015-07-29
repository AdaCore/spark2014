package body Other is
   Hidden : Integer := 0;  --  No abstract state exposes Hidden...

   procedure Initialize_G2 is
   begin
      G2 := 0;
   end Initialize_G2;

   package body Nested_Package is
   begin
      Nested_Package.Nested_Visible_Var := 0;
   end Nested_Package;
begin
   Initialize_G2;
end Other;
