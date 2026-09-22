pragma SPARK_Mode (On);

with Foo;

generic
procedure Lib_Subp
with Pre => Foo.Last + 1 = Foo.Last + 1;
pragma Annotate (GNATprove, Intentional, "overflow check", "Just a test");
