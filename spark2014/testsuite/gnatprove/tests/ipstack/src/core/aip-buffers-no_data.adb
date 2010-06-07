------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;

package body AIP.Buffers.No_Data
--# own State is Buffers, Free_List;
is
   subtype Buffer_Index is Positive range 1 .. Buffer_Num;

   type Buffer is record
      --  Next buffer in singly linked chain
      Next        : Buffer_Id;

      --  Reference to the actual data
      Payload_Ref : AIP.IPTR_T;

      --  Total length of the data referenced by this buffer
      Tot_Len     : Data_Length;

      --  The reference count always equals the number of pointers
      --  that refer to this buffer. This can be pointers from an application
      --  or the stack itself.
      Ref         : AIP.U16_T;
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buffers : Buffer_Array;
   Free_List : Buffer_Id := 1;  --  Head of the free-list

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Size   :     Data_Length;
      Buf    : out Buffer_Id)
   is
   begin
      AIP.Support.Verify (Free_List /= NOBUF);

      Buf                       := Free_List;
      Free_List                 := Buffers (Free_List).Next;

      Buffers (Buf).Next        := NOBUF;
      --  Caller must set this field properly, afterwards
      Buffers (Buf).Payload_Ref := AIP.NULIPTR;
      Buffers (Buf).Tot_Len     := Size;
      --  Set reference count
      Buffers (Buf).Ref         := 1;
   end Buffer_Alloc;

end AIP.Buffers.No_Data;
