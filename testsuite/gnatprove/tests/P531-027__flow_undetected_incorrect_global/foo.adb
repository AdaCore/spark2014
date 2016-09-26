package body Foo with SPARK_Mode => Off
is

   procedure Update is null;

   function read return Integer is (0);

end Foo;
