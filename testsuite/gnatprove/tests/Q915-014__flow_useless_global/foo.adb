package body Foo
  with Refined_State => (State => X)
is
   X : Boolean := False;

   procedure Stuff is
   begin
      null;
   end Stuff;

end Foo;
