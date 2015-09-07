package body Temperature_Buffer05
  --#own Contents is Buffer, Count, Next_In, Next_Out;
is
   Buffer_Size : constant := 8;
   type Buffer_Index_Type is mod Buffer_Size;
   type Buffer_Type is array (Buffer_Index_Type) of Temperature_Record;
   Buffer : Buffer_Type;

   type Buffer_Count_Type is range 0 .. Buffer_Size;
   Count    : Buffer_Count_Type; -- Number of items.
   Next_In  : Buffer_Index_Type; -- Next available slot.
   Next_Out : Buffer_Index_Type; -- Next item to extract.

   procedure Put (Item : in Temperature_Record)
   --# global in out Buffer, Count, Next_In, Next_Out;
   --# derives Buffer   from Buffer, Next_In, Item &
   --#         Count    from Count                 &
   --#         Next_In  from Next_In               &
   --#         Next_Out from Next_Out, Count;
   is
   begin
      -- Install the new item.
      Buffer (Next_In) := Item;
      Next_In := Next_In + 1;

      -- Adjust count, move Next_Out if necessary.
      if Count = Buffer_Size then
         Next_Out := Next_Out + 1;
      else
         Count := Count + 1;
      end if;
   end Put;


   function Has_More return Boolean
   --# global in Count;
   is
   begin
      return Count > 0;
   end Has_More;

   procedure Get (Item : out Temperature_Record)
   --# global in Buffer; in out Count, Next_Out;
   --# derives Item      from Next_Out, Buffer &
   --#         Count     from Count            &
   --#         Next_Out  from Next_Out;
   is
   begin
      Item := Buffer (Next_Out);
      Next_Out := Next_Out + 1;
      Count := Count - 1;
   end Get;


   procedure Clear
   --# global out Buffer, Count, Next_In, Next_Out;
   --# derives Buffer   from  &
   --#         Count    from  &
   --#         Next_In  from  &
   --#         Next_Out from  ;
   is
   begin
      Buffer   := Buffer_Type'(others => Temperature_Record'(Data_Types.Time_Initializer, 0));
      Count    := 0;
      Next_In  := 0;
      Next_Out := 0;
   end Clear;

end Temperature_Buffer05;
