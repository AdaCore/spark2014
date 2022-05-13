with Types; use Types;

procedure Foo (X : in out Ptr)
is
   Z : Ptr := X;
begin
   if Z.all > 10 then
      X := Z;
      --  Z := null;
      return;
   end if;

   Z.all := Z.all * 2;

   X := Z;
end Foo;
