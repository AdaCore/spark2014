------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;
with AIP.Conversions;

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

   subtype Buffer_Index is AIP.U16_T range 1 .. Buffer_Num;
   subtype Buffer_Count is Buffer_Index;

   type Buffer is record
      --  Next chunk in singly linked chain
      Next         : Buffer_Id;

      --  Number of chunks in singly linked chain
      Num          : Buffer_Count;

      --  Number of contiguous chunks in singly linked chain from this chunk
      Num_No_Jump  : Buffer_Count;

      --  Offset to get to the position of the actual data in the chunk
      Left_Offset  : Buffers.Chunk_Length;

      --  Offset from the right to the end of the actual data in the chunk
      Right_Offset : Buffers.Chunk_Length;

      --  Total length of this buffer, from the first to the last chunk in
      --  singly linked chain
      --
      --  The following invariant should hold:
      --  Tot_Len = Chunk_Length - Left_Offset - Right_Offset +
      --              (if Next /= 0 then Buffers (Next).Tot_Len else 0)
      Tot_Len      : Buffers.Data_Length;

      --  Kind of buffer
      Kind         : Buffers.Data_Buffer_Kind;

      --  The reference count always equals the number of pointers that refer
      --  to this buffer. This can be pointers from an application, the stack
      --  itself, or Next pointers from a chain.
      Ref          : AIP.U16_T;
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
         Cur_Buf                            := Next_Buf;
         Next_Buf                           := Buf_List (Cur_Buf).Next;

         --  Num and Num_No_Jump are as currently defined
         Buf_List (Cur_Buf).Num             := Remaining;
         Buf_List (Cur_Buf).Num_No_Jump     :=
           Buffer_Count'Min (Buf_List (Cur_Buf).Num_No_Jump, Remaining);

         --  Left offset is zero for all chunks but the first one
         if Remaining = Requested_Chunks then
            Buf_List (Cur_Buf).Left_Offset  := Offset;
         else
            Buf_List (Cur_Buf).Left_Offset  := 0;
         end if;

         --  Right offset is zero for all chunks but the last one
         if Remaining = 1 then
            Buf_List (Cur_Buf).Right_Offset :=
              Buffers.Chunk_Size - Remaining_Size;
         else
            Buf_List (Cur_Buf).Right_Offset := 0;
         end if;

         Buf_List (Cur_Buf).Tot_Len         :=
           Remaining_Size - Buf_List (Cur_Buf).Left_Offset;

         --  Remaining size decreases by Chunk_Size until last chunk
         if Remaining /= 1 then
            Remaining_Size                  :=
              Remaining_Size - Buffers.Chunk_Size;
         end if;

         Buf_List (Cur_Buf).Kind            := Kind;
         --  Set reference count
         Buf_List (Cur_Buf).Ref             := 1;
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
      Result : AIP.U16_T;
   begin
      case Buf_List (Buf).Kind is
         when Buffers.LINK_BUF =>
            Result := (Buffers.Chunk_Size - Buf_List (Buf).Left_Offset)
              - Buf_List (Buf).Right_Offset;
         when Buffers.MONO_BUF =>
            Result := Buf_List (Buf).Tot_Len;
      end case;
      return Result;
   end Buffer_Len;

   -----------------
   -- Buffer_Tlen --
   -----------------

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Tot_Len;
   end Buffer_Tlen;

   -----------------
   -- Buffer_Next --
   -----------------

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id
   --# global in Buf_List;
   is
   begin
      return Buf_List (Buf).Next;
   end Buffer_Next;

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

   ----------------
   -- Buffer_Ref --
   ----------------

   procedure Buffer_Ref (Buf : Buffer_Id)
   --# global in out Buf_List;
   is
   begin
      Buf_List (Buf).Ref := Buf_List (Buf).Ref + 1;
   end Buffer_Ref;

   -----------------
   -- Buffer_Free --
   -----------------

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T)
   --# global in out Buf_List, Free_List;
   is
      Cur_Buf, Next_Buf : Buffer_Id;
   begin
      Next_Buf   := Buf;
      N_Deallocs := 0;

      while Next_Buf /= Buffers.NOBUF loop
         --  Update iterators
         Cur_Buf  := Next_Buf;
         Next_Buf := Buf_List (Cur_Buf).Next;

         --  Decrease reference count
         Buf_List (Cur_Buf).Ref := Buf_List (Cur_Buf).Ref - 1;

         --  If reference count reaches zero, deallocate buffer
         if Buf_List (Cur_Buf).Ref = 0 then
            N_Deallocs := N_Deallocs + 1;
            --  Link to the head of the free-list
            Buf_List (Cur_Buf).Next           := Free_List;
            --  Update Num and Num_No_Jump fields only
            Buf_List (Cur_Buf).Num            := Buf_List (Free_List).Num + 1;
            if Free_List = Cur_Buf + 1 then
               Buf_List (Cur_Buf).Num_No_Jump :=
                 Buf_List (Free_List).Num_No_Jump + 1;
            else
               Buf_List (Cur_Buf).Num_No_Jump := 1;
            end if;
            --  Push to the head of the free-list
            Free_List                         := Cur_Buf;
         else
            --  Stop the iteration
            Next_Buf                          := Buffers.NOBUF;
         end if;
      end loop;
   end Buffer_Free;

end AIP.Buffers.Data;
