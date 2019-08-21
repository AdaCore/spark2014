package Test2 with
SPARK_Mode
is

   type Byte is mod 2**8;
   type Bytes is array (Natural range <>) of Byte;

   function Zero (Buffer : Bytes) return Natural is (0)
     with Pre => Buffer'Last = 10;

   function Check_Array (Buffer : Bytes) return Boolean is
     (Buffer'Last = 10
      and then Buffer'First = 0
      and then Buffer (Zero (Buffer) .. 0) = (0, 0));

end Test2;
