package Data_Buffer
with SPARK_Mode => On
is

private
   type Entry_Position_Type is mod 2 ** 64;
   type Header_Count_Type   is mod 2 ** 64;
   type Item_Size_Type      is mod 2 ** 64;
   type Item_Count_Type     is mod 2 ** 64;

   Page_Size : constant := 4096;

   type Writer_Buffer_Header_Type is
   record
      Header_Capacity : Header_Count_Type;
      Valid_Start     : Entry_Position_Type with Atomic;
      Valid_Stop      : Entry_Position_Type with Atomic;
      Item_Size       : Item_Size_Type;
      Item_Capacity   : Item_Count_Type;
   end record
   with
     Volatile,
     Async_Readers,
     Predicate => Valid_Stop - Valid_Start <= Entry_Position_Type (Header_Capacity),
     Size      => 5 * 8 * 8,
     Alignment => 8;

   for Writer_Buffer_Header_Type use
   record
      Header_Capacity at  0 range 0 .. (8 * 8) - 1;
      Valid_Start     at  8 range 0 .. (8 * 8) - 1;
      Valid_Stop      at 16 range 0 .. (8 * 8) - 1;
      Item_Size       at 24 range 0 .. (8 * 8) - 1;
      Item_Capacity   at 32 range 0 .. (8 * 8) - 1;
   end record;

end Data_Buffer;
