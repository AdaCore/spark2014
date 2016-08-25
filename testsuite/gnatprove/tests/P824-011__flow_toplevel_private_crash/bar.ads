with Foo;

use type Foo.T1;

--  Expected behaviour of this test is to *not* crash or infinitely loop
--  (this happened when compiling without assertions).

private package Bar with Elaborate_Body is

   type T2 is record
      C : Boolean;
   end record;

end Bar;
