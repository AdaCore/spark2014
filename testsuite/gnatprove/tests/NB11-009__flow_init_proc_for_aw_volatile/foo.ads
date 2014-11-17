package Foo
with SPARK_Mode
is

   type Volatile_Type is record
      Header : Natural with Atomic;
      Data   : Natural with Atomic;
   end record
     with Volatile;

   procedure Init
     (Item : in out Volatile_Type;
      Data :        Natural)
   with
       Depends => (Item =>+ Data);

end Foo;
