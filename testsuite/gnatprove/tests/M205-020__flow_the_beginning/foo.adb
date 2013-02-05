procedure Foo (A    : in     Boolean;
	       X, Y : in out Integer)
is
begin

   if A then
      return;
   else
      X := 1;
   end if;
   Y := 0;

end Foo;
