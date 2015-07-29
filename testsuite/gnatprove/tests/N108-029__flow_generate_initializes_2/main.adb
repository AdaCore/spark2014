with Generate_Initializes; use Generate_Initializes;

procedure Main (X : out Integer) is
begin
   X := A + Nested.Visible_Var + Nested.Foo;
end Main;
