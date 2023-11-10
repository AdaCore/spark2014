with Bar;
package body Foo with SPARK_Mode is
   D : Integer := Bar.C;

   procedure P is null;
end Foo;
