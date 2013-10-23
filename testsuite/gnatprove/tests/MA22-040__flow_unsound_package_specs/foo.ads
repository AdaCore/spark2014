package Foo
  with SPARK_Mode, Initializes => X
is
   -- This package must NOT have a body, owing to lack
   -- of declarations and no Elaborate_Body, but flow
   -- analysis should still pick up that the
   -- following declaration does not match the
   -- Initializes contract above.

   X : Integer;
end Foo;
