package body Foo
is
   X : Integer := 0;
   Y : Integer;
   Z : Integer;
   W : Integer := 0; --  ineffective
begin
   Y := 0;
   Z := 0;  --  ineffective
   if True then --  ineffective
      Z := 0;  --  ineffective
   end if;
   if True then
      Z := 0;
   else
      Z := 1;
   end if;
   W := 10;
end Foo;
