with Foo;

procedure Main
is
   procedure Run
   with
      Pre  => Foo.Valid (Foo.Get_State),
      Post => Foo.Valid (Foo.Get_State)
   is
   begin
      null;
   end Run;

begin
   null;
end Main;
