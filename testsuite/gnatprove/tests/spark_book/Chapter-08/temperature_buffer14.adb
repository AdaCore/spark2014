package body Temperature_Buffer14
  with
    SPARK_Mode    => On,
    Refined_State => (Contents => (Buffer, Count, Next_In, Next_Out))
is
   Buffer_Size : constant := 8;
   type Buffer_Index_Type is mod Buffer_Size;
   type Buffer_Type is array (Buffer_Index_Type) of Temperature_Record;
   Buffer : Buffer_Type;

   type Buffer_Count_Type is range 0 .. Buffer_Size;
   Count        : Buffer_Count_Type; -- Number of items in the buffer.
   Next_In      : Buffer_Index_Type; -- Points at the next available slot.
   Next_Out     : Buffer_Index_Type; -- Points at the next item to extract.

   procedure Put (Item : in Temperature_Record)
     with
       Refined_Global => (In_Out => (Buffer, Count, Next_In, Next_Out)),
       Refined_Depends =>
         (Buffer   =>+ (Next_In, Item),
          Count    =>+ null,
          Next_In  =>+ null,
          Next_Out =>+ Count)
   is
   begin
      -- Install the new item.
      Buffer (Next_In) := Item;
      Next_In := Next_In + 1;

      -- Adjust count, move Next_Out if necessary (old items deleted from a full buffer).
      if Count = Buffer_Size then
         Next_Out := Next_Out + 1;
      else
         Count := Count + 1;
      end if;
   end Put;


   function Has_More return Boolean is (Count > 0)
     with Refined_Global => (Input => Count);

   procedure Get (Item : out Temperature_Record)
     with
       Refined_Global => (Input => Buffer, In_Out => (Count, Next_Out)),
       Refined_Depends =>
         (Item     => (Next_Out, Buffer),
          Count    =>+ null,
          Next_Out =>+ null)
   is
   begin
      Item := Buffer (Next_Out);
      Next_Out := Next_Out + 1;
      Count := Count - 1;
   end Get;


   procedure Clear
     with
       Refined_Global => (Output => (Buffer, Count, Next_In, Next_Out)),
       Refined_Depends =>
         ((Buffer, Count, Next_In, Next_Out) => null)
   is
   begin
      Buffer   := Buffer_Type'(others => Temperature_Record'(Data_Types.Time_Initializer, 0));
      Count    := 0;
      Next_In  := 0;
      Next_Out := 0;
   end Clear;

end Temperature_Buffer14;
