package body Bar
with
   SPARK_Mode
is

   -------------------------------------------------------------------------

   procedure Init
   is
   begin
      Foo.Init (Item => Instance,
                Data => 0);
   end Init;

end Bar;
