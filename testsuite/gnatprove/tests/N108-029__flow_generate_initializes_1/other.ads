package Other is
   G  : Integer := 0;
   G2 : Integer;

   procedure Initialize_G2;

   package Nested_Package is
      Nested_Visible_Var : Integer;
   end Nested_Package;
end Other;
