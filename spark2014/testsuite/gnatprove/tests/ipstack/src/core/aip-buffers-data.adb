------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;

package body AIP.Buffers.Data
--# own State is Data_Array, Buf_List, Free_List;
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

   subtype Chunk_Position is AIP.U16_T range 1 .. Buffers.Chunk_Size;
   subtype Buffer_Index is AIP.U16_T range 1 .. Buffer_Num;
   subtype Buffer_Count is Buffer_Index;

   type Buffer is record
      --  Next buffer in singly linked chain
      Next        : Buffer_Id;

      --  Number of chunks in the linked chain
      Num         : Buffer_Count;

      --  Number of chunks in the linked chain that form a contiguous chain
      Num_No_Jump : Buffer_Count;

      --  Position of the actual data in the chunk
      Payload_Pos : Chunk_Position;

      --  Length of the actual data in the chunk
      Len         : Buffers.Chunk_Length;

      --  Total length of this buffer and all next buffers in chain belonging
      --  to the same packet
      --
      --  The following invariant should hold:
      --  Tot_Len = Len + (if Next /= 0 then Buffers (Next).Tot_Len else 0)
      Tot_Len     : Buffers.Data_Length;

      --  Kind of buffer
      Kind        : Buffers.Data_Buffer_Kind;

      --  The reference count always equals the number of pointers
      --  that refer to this buffer. This can be pointers from an application,
      --  the stack itself, or Next pointers from a chain.
      Ref         : AIP.U16_T;
   end record;

   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buf_List  : Buffer_Array;
   Free_List : Buffer_Id;  --  Head of the free-list

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Buffers.Offset_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id)
   --# global in out Buf_List, Free_List;
   is
      Requested_Size    : AIP.U16_T;
      Requested_Chunks  : AIP.U16_T;
      Cur_Buf, Next_Buf : Buffer_Id;
      Remaining_Size    : Buffers.Data_Length;
      --  Remaining size to be allocated
   begin
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

      --  Allocate the first chunk
      Buf            := Free_List;
      Cur_Buf        := Buf;
      Next_Buf       := Buf_List (Cur_Buf).Next;
      Remaining_Size := Requested_Size;

      --  Allocate the remaining chunks
      for Remaining in reverse AIP.U16_T range 1 .. Requested_Chunks loop
         Buf_List (Cur_Buf).Num            := Remaining;
         Buf_List (Cur_Buf).Num_No_Jump    :=
           Buffer_Count'Min (Buf_List (Cur_Buf).Num_No_Jump, Remaining);

         --  Payload_Pos is one for all chunks but the first one
         if Remaining = Requested_Chunks then
            Buf_List (Cur_Buf).Payload_Pos := Offset + 1;
         else
            Buf_List (Cur_Buf).Payload_Pos := 1;
         end if;
         Remaining_Size                   :=
           Remaining_Size - Buf_List (Cur_Buf).Payload_Pos;

         --  Total length from this buffer is Remaining_Size at this point
         Buf_List (Cur_Buf).Tot_Len        := Remaining_Size;

         Buf_List (Cur_Buf).Len            :=
           AIP.U16_T'Min (Buffers.Chunk_Size, Remaining_Size);
         Remaining_Size                   :=
           Remaining_Size - Buf_List (Cur_Buf).Len;

         Buf_List (Cur_Buf).Kind           := Kind;
         --  Set reference count
         Buf_List (Cur_Buf).Ref            := 1;
      end loop;

      --  Remove the allocate chunks from the free-list
      Buf_List (Cur_Buf).Next := Buffers.NOBUF;
      Free_List := Next_Buf;
   end Buffer_Alloc;

   ----------------
   -- Buffer_Len --
   ----------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Len;
   end Buffer_Len;

end AIP.Buffers.Data;

