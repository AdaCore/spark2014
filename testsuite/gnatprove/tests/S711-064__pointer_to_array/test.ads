package Test with
SPARK_Mode
is

   type Byte is mod 2**8;
   type Bytes is array (Natural range <>) of Byte;
   type Bytes_Ptr is not null access Bytes;

   function Check_Array_Ptr (Buffer : Bytes_Ptr) return Boolean is
     (Buffer'First <= (Natural'Last / 2)
      and then Buffer'Length >= 14
      and then Buffer.all (Buffer'First + 12 .. Buffer'First + 13) = (0, 0)
      and then Buffer.all (Buffer'First + 12 .. Buffer'First + 13) = (0, 0));  --  @OVERFLOW_CHECK:PASS

   function Check_Array (Buffer : Bytes) return Boolean is
     (Buffer'First <= (Natural'Last / 2)
      and then Buffer'Length >= 14
      and then Buffer (Buffer'First + 12 .. Buffer'First + 13) = (0, 0)
      and then Buffer (Buffer'First + 12 .. Buffer'First + 13) = (0, 0));

end Test;
