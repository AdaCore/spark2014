package Foo is

   type T is private;

   procedure Fnark (X : in out T)
   with Global => null;

private
   pragma SPARK_Mode (Off);

   type T is new Integer;

end Foo;
