procedure Foo (A       : in     Boolean;
	       X, Y, Z : in out Integer)
is
   B : Boolean;
begin

   if A or B then
      return;
   else
      X := 0;
   end if;
   Y := 0;

end Foo;
