pragma SPARK_Mode;

with Foo;
with Generic_Bar;

package Bar is new Generic_Bar (Foo.Context_Type, Foo.Initialize, Foo.Valid);
