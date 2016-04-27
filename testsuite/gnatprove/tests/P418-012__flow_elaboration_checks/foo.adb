package body Foo is
   procedure P is null;
   Val : Boolean;

   package Nested is
      X : Boolean := False;
   end Nested;

   package body Nested is
   begin
      X := not X;
   end Nested;

begin
   Body_Elaborated := True;   --  bad
   Foo.B := False;            --  bad
   Baz   := 1;                --  maybe bad?
   Val   := False;            --  ok
end Foo;
