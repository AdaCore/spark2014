package Bytes with SPARK_Mode is

   type UInt8 is mod 2**8;
   type UInt16 is mod 2**16;

   type ByteArray is array(UInt16 range <>) of UInt8;

   type Record_Struct is record
      id: UInt16;
      length : UInt8;
      Payload : ByteArray(1..256);
   end record;

   procedure To_Byte_Array (A_Record: in Record_Struct; output : out ByteArray; length : out UInt16);

end Bytes;
