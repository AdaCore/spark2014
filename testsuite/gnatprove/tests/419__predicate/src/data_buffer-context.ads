with Filler;

generic
   type Header_Type is private;
   Null_Header : Header_Type;
   Header_Capacity : Positive;

   type Item_Type is private;
   Null_Item : Item_Type;
   Item_Capacity : Positive;

package Data_Buffer.Context
with SPARK_Mode => On
is

   type Writer_Context_Type is limited private;

   procedure Initialize (Context : out Writer_Context_Type)
   with Always_Terminates;

private

   type Item_Index_Type is new Natural range 0 .. Item_Capacity;

   type Item_Array is array (Item_Index_Type) of Item_Type with Pack;


   type Entry_Index_Type is new Natural range 0 .. Header_Capacity;

   type Entry_Type is record
      Start  : Natural;
      Length : Natural;
      Header : Header_Type;
   end record;

   Null_Entry : constant Entry_Type := (Start  => 0,
                                        Length => 0,
                                        Header => Null_Header);

   type Entry_Array is array (Entry_Index_Type) of Entry_Type with Pack;


   pragma Compile_Time_Error (Writer_Buffer_Header_Type'Size
                              + Entry_Array'Size
                              + Item_Array'Size
                              > Long_Long_Long_Integer (Long_Long_Integer'Last),
                              "Shared memory buffer too large.");

   Writer_Buffer_Size : constant Long_Long_Integer
     := Writer_Buffer_Header_Type'Size
        + Entry_Array'Size
        + Item_Array'Size;

   package Writer_Filler_Package is new Filler (Buffer_Bits => Writer_Buffer_Size);

   type Writer_Context_Type is
   record
      Header       : Writer_Buffer_Header_Type;
      Entry_Buffer : Entry_Array;
      Item_Buffer  : Item_Array;
      Filler       : Writer_Filler_Package.Filler_Type;
   end record
   with
     Volatile,
     Async_Readers,
     Predicate => Writer_Context_Type.Header.Header_Capacity
                    = Header_Count_Type (Header_Capacity) and
                  Writer_Context_Type.Header.Item_Capacity
                    = Item_Count_Type (Item_Capacity),
     Alignment => Page_Size;

   type Packed_Writer_Context_Type is
   record
      Header       : Writer_Buffer_Header_Type;
      Entry_Buffer : Entry_Array;
      Item_Buffer  : Item_Array;
      Filler       : Writer_Filler_Package.Filler_Type;
   end record
   with
     Volatile,
     Async_Readers,
     Pack,
     Alignment => Page_Size;

end Data_Buffer.Context;
