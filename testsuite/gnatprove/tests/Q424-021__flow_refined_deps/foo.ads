pragma SPARK_Mode;

package Foo
is

   F : Integer := 0;

   function Get return Integer
     with
     Global => (Input => F);

end Foo;
