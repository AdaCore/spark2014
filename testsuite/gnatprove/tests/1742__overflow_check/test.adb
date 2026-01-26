with Interfaces; use Interfaces;

procedure Test with spark_mode is

   type Byte_Array_T is array (Integer_128 range <>) of Boolean;

   procedure Potato (Data : Byte_Array_T) with Pre => Data'First > -128;

   procedure Potato (Data : Byte_Array_T)
   is
   begin
      if Integer_128 (Data'Length) > 42 then -- @OVERFLOW_CHECK:FAIL
         null;
      end if;
   end Potato;

begin
   null;
end;
