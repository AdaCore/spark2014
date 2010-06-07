------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Support;

--# inherit AIP.Support;

package body AIP.Buffers
--# own State is Data, Buffers, Free_List;
is

   --  All data is stored in a statically allocated array Data, while data
   --  structures to manage the allocation of pieces of this array to
   --  buffers are stored in another statically allocated array Buffers.

   --  This division allows the allocation of contiguous pieces of the Data
   --  array to a single buffer, so as to simulate the allocation of a single
   --  chunk of memory, which is required for MONO_BUF buffers.

   subtype Data_Index is Data_Length;
   type Data_Array is array (Data_Index) of Element;

   Data : Data_Array;

   subtype Chunk_Index is Positive range 1 .. Chunk_Num;
   subtype Chunk_Position is Positive range 1 .. Chunk_Size;

   type Buffer is record
      --  Next chunk in singly linked chain
      Next        : Chunk_Index;

      --  Position of the actual data in the chunk (Kind = (MONO|LINK)_BUF)
      Payload_Pos : Chunk_Position;

      --  Reference to the actual data (Kind = REF_BUF)
      Payload_Ref : AIP.IPTR_T;

      --  Length of this chunk
      Len         : Chunk_Length;

      --  Total length of this buffer and all next buffers in chain belonging
      --  to the same packet
      --
      --  The following invariant should hold:
      --  Tot_Len = Len + (if Next /= 0 then Buffers (Next).Tot_Len else 0)
      Tot_Len     : Data_Length;

      --  Kind of buffer
      Kind        : Buffer_Kind;

      --  The reference count always equals the number of pointers
      --  that refer to this buffer. This can be pointers from an application,
      --  the stack itself, or Next pointers from a chain.
      Ref         : AIP.U16_T;
   end record;

   subtype Buffer_Index is Positive range 1 .. Buffer_Num;
   type Buffer_Array is array (Buffer_Index) of Buffer;

   Buffers   : Buffer_Array;
   Free_List : Buffer_Id := 1;  --  Head of the free-list

   ------------------
   -- Buffer_Alloc --
   ------------------

   procedure Buffer_Alloc
     (Offset :     Chunk_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id)
   is

   begin
      case Kind is
         when LINK_BUF =>
            AIP.Support.Verify (Size <= Buffers (Free_List).Tot_Len);
            null;
         when MONO_BUF =>
            null;
         when REF_BUF =>
            null;
      end case;
   end Buffer_Alloc;

end AIP.Buffers;
