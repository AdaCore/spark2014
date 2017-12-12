package body Parent.Privchild is
   procedure Foo is null;
   Child_Body_Var   : Integer := 0;
   Child_Body_Const : constant Integer := Q.F;
end;
