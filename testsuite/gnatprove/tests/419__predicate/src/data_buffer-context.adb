package body Data_Buffer.Context
with SPARK_Mode => On
is

   pragma Compile_Time_Error (Writer_Context_Type'Size /= Packed_Writer_Context_Type'Size,
                              "Writer_Context_Type is not naturally packed.");

   procedure Initialize (Context : out Writer_Context_Type)
   is
   begin
      Context.Header := (Header_Capacity => Header_Count_Type (Header_Capacity),
                         Item_Size       => Item_Type'Size,
                         Item_Capacity   => Item_Count_Type (Item_Capacity),
                         Valid_Start     => 0,
                         Valid_Stop      => 0);

      Context.Entry_Buffer := (others => Null_Entry);
      Context.Item_Buffer  := (others => Null_Item);
      Context.Filler       := (others => 0);
   end Initialize;

end Data_Buffer.Context;
