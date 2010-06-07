------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;

package body AIP.Buffers.No_Data
--# own State is Buf_List, Free_List;
is
   subtype Buffer_Index is Positive range 1 .. Buffer_Num;

   type Buffer is record
      --  Next buffer in singly linked chain
      Next        : Buffer_Id;

      --  Reference to the actual data
      Payload_Ref : AIP.IPTR_T;

      --  Total length of the data referenced by this buffer
      Tot_Len     : Buffers.Data_Length;

      --  The reference count always equals the number of pointers
      --  that refer to this buffer. This can be pointers from an application
      --  or the stack itself.
      Ref         : AIP.U16_T;
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buf_List  : Buffer_Array;
   Free_List : Buffer_Id;  --  Head of the free-list

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Size   :     Buffers.Data_Length;
      Buf    : out Buffer_Id)
   --# global in out Buf_List, Free_List;
   is
   begin
      Support.Verify (Free_List /= Buffers.NOBUF);

      Buf                       := Free_List;
      Free_List                 := Buf_List (Free_List).Next;

      Buf_List (Buf).Next        := Buffers.NOBUF;
      --  Caller must set this field properly, afterwards
      Buf_List (Buf).Payload_Ref := AIP.NULIPTR;
      Buf_List (Buf).Tot_Len     := Size;
      --  Set reference count
      Buf_List (Buf).Ref         := 1;
   end Buffer_Alloc;

end AIP.Buffers.No_Data;
