------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

--# inherit AIP.Buffers, AIP.Buffers.Common, AIP.Support, AIP.Conversions;

private package AIP.Buffers.Data
--# own State, Free_List;
is
   --  There is one data buffer per chunk
   Buffer_Num : constant AIP.U16_T := Buffers.Chunk_Num;

   subtype Buffer_Id is AIP.U16_T range 0 .. Buffer_Num;

   Free_List : Buffer_Id;  --  Head of the free-list for data buffers

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset :     Buffers.Offset_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out Common.Buf_List, State, Free_List;
   --  Allocate and return a new Buf of kind Kind, aimed at holding Size
   --  elements of data starting at offset Offset

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T;
   --# global in State;
   --  Pointer to data held by buffer Buf

   ----------------------------------
   -- Buffer reference and release --
   ----------------------------------

   procedure Buffer_Link (Buf : Buffer_Id; Next : Buffer_Id);
   --# global in out State;
   --  Link buffer Buf to buffer Next

end AIP.Buffers.Data;
