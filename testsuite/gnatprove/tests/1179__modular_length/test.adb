procedure Test with spark_mode is

   type Byte is mod 2**8;

   type Unsigned_64 is mod 2**64;

   type Byte_Array_T is array (Unsigned_64 range <>) of Byte;

   procedure Potato (Data : Byte_Array_T) with Pre => Data'First > 0;

   procedure Potato (Data : Byte_Array_T)
   is
   begin
      if Unsigned_64 (Data'Length) > 42 then
         null;
      end if;
   end Potato;

   procedure Potato_2 (Data : Byte_Array_T) with Pre => Data'First > 0;

   procedure Potato_2 (Data : Byte_Array_T)
   is
   begin
      if Unsigned_64'(Data'Length) > 42 then
         null;
      end if;
   end Potato_2;

begin
   null;
end;
