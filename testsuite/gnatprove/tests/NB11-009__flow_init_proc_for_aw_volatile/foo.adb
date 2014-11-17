package body Foo
with SPARK_Mode
is

   -------------------------------------------------------------------------

   procedure Init
     (Item : in out Volatile_Type;
      Data :        Natural)
   is
   begin
      Item := Volatile_Type'(Header => 0,
                             Data   => Data);
   end Init;

end Foo;
