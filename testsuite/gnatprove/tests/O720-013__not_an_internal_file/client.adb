with Foo;
with A.Foo; -- GNAT wants this in file "a~foo.ads" but GNATprove is happy with "a-foo.ads"
with I.Foo;
with Q.Foo;

procedure Client is
begin
   Foo.Dummy;
   A.Foo.Dummy;
   I.Foo.Dummy;
   Q.Foo.Dummy;
end;
