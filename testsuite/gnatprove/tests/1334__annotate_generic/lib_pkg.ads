pragma SPARK_Mode (On);

with Foo;

generic
package Lib_Pkg is
   procedure Bar
   with Pre => Foo.Last + 1 = Foo.Last + 1;
end Lib_Pkg;
pragma Annotate (GNATprove, Intentional, "overflow check", "Just a test");
