package body Ordering_Buffers with SPARK_Mode is

   procedure Set_Message_Impl (
     Buffer  : in out Ordering_Buffer_Type;
     Index   : in     Sequence_Number_Type;
     Message : in     Message_Pointer
   ) with Pre => (First (Buffer) <= Index and Index <= Last (Buffer)),
     Post => First (Buffer) = First (Buffer'Old) and
       Get_Message (Buffer, Index) = Message and
         (for all I in First (Buffer) .. Last (Buffer) =>
           (if I /= Index then Get_Message (Buffer, I) = Get_Message (Buffer'Old, I)));
   --  Same as Set_Message, but doesn't require that there be no existing
   --  message.

   -------------------
   -- Advance_First --
   -------------------

   procedure Advance_First (Buffer : in out Ordering_Buffer_Type) is
   begin
      Buffer.First := Buffer.First + 1;
   end Advance_First;

   -------------------
   -- Consume_First --
   -------------------

   procedure Consume_First (
     Buffer  : in out Ordering_Buffer_Type;
     Message :    out Message_Pointer
   ) is
      Orig_First : constant Slightly_Extended_Sequence_Number_Type
        := First (Buffer);
   begin
      Message := Get_Message (Buffer, Orig_First);
      Set_Message_Impl (Buffer, Orig_First, Null_Message);
      pragma Assert (not Has_Message (Buffer, Orig_First));
      Advance_First (Buffer);
      pragma Assert (Last (Buffer) = Orig_First + Ordering_Buffer_Length);
      pragma Assert (Ring_Index_Type'Mod (Last (Buffer)) = Ring_Index_Type'Mod (Orig_First + Ordering_Buffer_Length));
      pragma Assert (Ring_Index_Type'Mod (Orig_First + Ordering_Buffer_Length) = Ring_Index_Type'Mod (Orig_First));
      pragma Assert (Ring_Index_Type'Mod (Ordering_Buffer_Length) = 0);
      pragma Assert (Ring_Index_Type'Mod (Last (Buffer)) = Ring_Index_Type'Mod (Orig_First));
      pragma Assert (Ring_Index_Type'Mod (Last (Buffer) - Orig_First) = 0);
      pragma Assert (Ring_Index_Type'Mod (Last (Buffer)) = Ring_Index_Type'Mod (Orig_First));
      pragma Assert (Has_Message (Buffer, Orig_First) = Has_Message (Buffer, Last (Buffer)));
   end Consume_First;

   -----------------
   -- Set_Message --
   -----------------

   procedure Set_Message (
     Buffer  : in out Ordering_Buffer_Type;
     Index   : in     Sequence_Number_Type;
     Message : in     Message_Pointer
   ) is
   begin
      Set_Message_Impl (Buffer, Index, Message);
   end Set_Message;

   ----------------------
   -- Set_Message_Impl --
   ----------------------

   procedure Set_Message_Impl (
     Buffer  : in out Ordering_Buffer_Type;
     Index   : in     Sequence_Number_Type;
     Message : in     Message_Pointer
   ) is
      Ring_Index : constant Ring_Index_Type := Ring_Index_Type'Mod (Index);
   begin
      Buffer.Ring (Ring_Index) := Message;
      pragma Assert (for all I in First (Buffer) .. Last (Buffer) =>
        -Ordering_Buffer_Length < I - Index and
          I - Index < Ordering_Buffer_Length);
      pragma Assert (for all I in Extended_Sequence_Number_Type =>
        (if -Ordering_Buffer_Length < I - Index and
          I - Index < 0 then Ring_Index_Type'Mod (I) /= Ring_Index_Type'Mod (Index)));
      pragma Assert (for all I in Extended_Sequence_Number_Type =>
        (if 0 < I - Index and I - Index < Ordering_Buffer_Length then
          Ring_Index_Type'Mod (I) /= Ring_Index_Type'Mod (Index)));
      pragma Assert (for all I in First (Buffer) .. Last (Buffer) =>
        (if I /= Index then Ring_Index_Type'Mod (I) /= Ring_Index));
   end Set_Message_Impl;

end Ordering_Buffers;
