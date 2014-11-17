with Foo;

package Bar
with
   SPARK_Mode
is

   Instance : Foo.Volatile_Type
     with Async_Readers, Async_Writers;

   procedure Init;

end Bar;
