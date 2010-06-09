------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;
with AIP.Conversions;
with AIP.Buffers.Common;

package body AIP.Buffers.Data
--# own State is Data_Array, Buf_List;
is
   --  All data is stored in a statically allocated array Data_Array, while
   --  data structures to manage the allocation of pieces of this array to
   --  buffers are stored in another statically allocated array Buffers.

   --  This division allows the allocation of contiguous pieces of the
   --  Data_Array array to a single buffer, so as to simulate the allocation
   --  of a single chunk of memory, which is required for MONO_BUF buffers.

   subtype Data_Index is Buffers.Data_Length;
   type Data_Array_Type is array (Data_Index) of Buffers.Elem;

   Data_Array : Data_Array_Type;

   subtype Buffer_Count is Buffers.Buffer_Index;

   type Buffer is record
      --  Number of chunks in singly linked chain
      Num          : Buffer_Count;

      --  Number of contiguous chunks in singly linked chain from this chunk
      Num_No_Jump  : Buffer_Count;

      --  Offset to get to the position of the actual data in the chunk
      Left_Offset  : Buffers.Chunk_Length;

      --  Kind of buffer
      Kind         : Buffers.Data_Buffer_Kind;
   end record;

   type Buffer_Array is array (Buffers.Buffer_Index) of Buffer;

   Buf_List : Buffer_Array;

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Buffers.Offset_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id)
   --# global in out Common.Buf_List, Buf_List, Free_List;
   is
      Requested_Size    : AIP.U16_T;
      Requested_Chunks  : AIP.U16_T;
      Cur_Buf, Next_Buf : Buffer_Id;
      Remaining_Size    : Buffers.Data_Length;
      --  Remaining size to be allocated
   begin
      --  Check that the free-list is not empty
      Support.Verify (Free_List /= Buffers.NOBUF);

      Requested_Size := Offset + Size;
      if Requested_Size = 0 then
         Requested_Chunks := 1;
      else
         Requested_Chunks :=
           (Requested_Size + (Buffers.Chunk_Size - 1)) / Buffers.Chunk_Size;
      end if;

      --  Check that the requested number of chunks are available, and that
      --  they form a contiguous chain of chunks for Kind = MONO_BUF
      case Kind is
         when Buffers.LINK_BUF =>
            Support.Verify (Requested_Chunks <= Buf_List (Free_List).Num);
         when Buffers.MONO_BUF =>
            Support.Verify
              (Requested_Chunks <= Buf_List (Free_List).Num_No_Jump);
      end case;

      --  Pop the head of the free-list
      Buf            := Free_List;
      Cur_Buf        := Buf;  --  Useless because loop always executes
                              --  Added to ensure Cur_Buf is initialized anyway
      Next_Buf       := Buf;
      Remaining_Size := Requested_Size;

      --  Allocate chunks in singly linked chain
      for Remaining in reverse AIP.U16_T range 1 .. Requested_Chunks loop
         --  Update iterators
         Cur_Buf                             := Next_Buf;
         Next_Buf                            := Common.Buf_List (Cur_Buf).Next;

         --  Num and Num_No_Jump are as currently defined
         Buf_List (Cur_Buf).Num              := Remaining;
         Buf_List (Cur_Buf).Num_No_Jump      :=
           Buffer_Count'Min (Buf_List (Cur_Buf).Num_No_Jump, Remaining);

         --  Left offset is zero for all chunks but the first one
         if Remaining = Requested_Chunks then
            Buf_List (Cur_Buf).Left_Offset   := Offset;
         else
            Buf_List (Cur_Buf).Left_Offset   := 0;
         end if;

         Common.Buf_List (Cur_Buf).Tot_Len   :=
           Remaining_Size - Buf_List (Cur_Buf).Left_Offset;

         --# accept F, 41, "Expression is stable";
         case Kind is
            when Buffers.LINK_BUF =>
               --  Length completes offset to chunk size unless not enough data
               --  remaining
               Common.Buf_List (Cur_Buf).Len :=
                 AIP.U16_T'Min (Buffers.Chunk_Size
                                - Buf_List (Cur_Buf).Left_Offset,
                                Common.Buf_List (Cur_Buf).Tot_Len);
            when Buffers.MONO_BUF =>
               --  Length is same as total length
               Common.Buf_List (Cur_Buf).Len :=
                 Common.Buf_List (Cur_Buf).Tot_Len;
         end case;
         --# end accept;

         --  Remaining size decreases by Chunk_Size until last chunk
         if Remaining /= 1 then
            Remaining_Size                   :=
              Remaining_Size - Buffers.Chunk_Size;
         end if;

         Buf_List (Cur_Buf).Kind             := Kind;
         --  Set reference count
         Common.Buf_List (Cur_Buf).Ref       := 1;
      end loop;

      --  Remove the allocate chunks from the free-list
      Common.Buf_List (Cur_Buf).Next := Buffers.NOBUF;
      Free_List                      := Next_Buf;
   end Buffer_Alloc;

   --------------------
   -- Buffer_Payload --
   --------------------

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T
   --# global in Data_Array, Buf_List;
   is
      --# hide Buffer_Payload;  --  Hidden because of 'Address attribute
   begin
      return Conversions.To_IPTR (Data_Array (Buf)'Address)
        + AIP.IPTR_T (Buf_List (Buf).Left_Offset);
   end Buffer_Payload;

   -----------------
   -- Buffer_Link --
   -----------------

   procedure Buffer_Link (Buf : Buffer_Id; Next : Buffer_Id)
   --# global in out Buf_List;
   is
   begin
      --  Update Num and Num_No_Jump fields only
      Buf_List (Buf).Num            := Buf_List (Next).Num + 1;
      if Next = Buf + 1 then
         Buf_List (Buf).Num_No_Jump := Buf_List (Next).Num_No_Jump + 1;
      else
         Buf_List (Buf).Num_No_Jump := 1;
      end if;
   end Buffer_Link;

end AIP.Buffers.Data;
