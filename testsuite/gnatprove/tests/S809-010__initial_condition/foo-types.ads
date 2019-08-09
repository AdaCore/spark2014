package Foo.Types
is

   function Foobar return Boolean
   with Ghost;

private

   function Foobar return Boolean
   is (True);

end Foo.Types;
