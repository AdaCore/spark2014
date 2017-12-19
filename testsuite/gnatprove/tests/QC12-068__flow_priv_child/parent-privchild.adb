package body Parent.Privchild is
   procedure Foo is null;
   Child_Body_Var   : Integer := 0;
   Child_Body_Const : constant Integer := Q.F;

   package Nested is
      Nested_In_Child_Var   : Integer := 0;
      Nested_In_Child_Const : constant Integer := Q.F;

      package Nested_Nested is
         Nested_Nested_In_Child_Var   : Integer := 0;
         Nested_Nested_In_Child_Const : constant Integer := Q.F;
      end;
   end;

   package body Nested is
      package body Nested_Nested is
      begin
         null;
      end;
   begin
      null;
   end;
end;
