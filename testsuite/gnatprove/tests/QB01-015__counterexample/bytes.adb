package body Bytes with SPARK_Mode is

   procedure To_Byte_Array (A_Record: in Record_Struct; output : out ByteArray; length : out UInt16) is
   begin
      output(output'First) := A_Record.length;  -- @COUNTEREXAMPLE
   end To_Byte_Array;

end Bytes;
