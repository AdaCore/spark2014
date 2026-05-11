with System.Storage_Elements;

package body Buffers
with
  SPARK_Mode,
  Refined_State => (State => (Buffer_Table))
is

   use type Types.Buffer_Range;

   Buffer_Table : Types.Buffer_Array (Types.Buffer_Range)
     := (others => Types.Buffer_Type'(Base_Address   => System.Null_Address,
                                      Base_Index     => 1,
                                      First          => 0));

   -----------------------------------------------------------------------------

   function Map_Address (Buffer : Types.Buffer_Range) return Types.Buffer_Address_Type
   is
      package S renames System.Storage_Elements;
      use all type S.Storage_Offset, Types.Data_Range;

      Pix_Bytes  : constant S.Storage_Offset := Types.Data_Type'Size / 8;
      Base_Index : constant Types.Data_Range := Buffer_Table (Buffer).Base_Index;
      First      : constant Types.Data_Range := Buffer_Table (Buffer).First;
      Offset     : constant S.Storage_Offset
        := S.Storage_Offset ((First - Base_Index)) * Pix_Bytes;
   begin
      return Buffer_Table (Buffer).Base_Address + Offset;
   end Map_Address;

   -----------------------------------------------------------------------------

end Buffers;
