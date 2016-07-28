with Bar;

procedure Foo
is
   function Id (B : Boolean) return Boolean is (B);
begin
   pragma Assert (Id (True));
   Bar.Hello;
end Foo;
