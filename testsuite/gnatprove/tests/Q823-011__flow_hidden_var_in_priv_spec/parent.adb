package body Parent
  with Refined_State => (State => C)
is
   C : Integer;

   procedure Foo is null;

end;
