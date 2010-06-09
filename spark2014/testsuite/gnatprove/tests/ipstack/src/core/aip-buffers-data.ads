------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

--# inherit AIP.Buffers, AIP.Support, AIP.Conversions;

private package AIP.Buffers.Data
--# own State;
is
   --  There is one data buffer per chunk
   Buffer_Num : constant AIP.U16_T := Buffers.Chunk_Num;

   subtype Buffer_Id is AIP.U16_T range 0 .. Buffer_Num;

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset :     Buffers.Offset_Length;
      Size   :     Buffers.Data_Length;
      Kind   :     Buffers.Data_Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding Size
   --  elements of data starting at offset Offset

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of packet data held
   --  - in the first chunk of buffer Buf for Kind = LINK_BUF
   --  - in all chunks of buffer Buf for Kind = MONO_BUF

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of packet data held in all chunks of buffer Buf

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id;
   --# global in State;
   --  Buffer following Buf in a chain, either next buffer for the same packet
   --  or NOBUF

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T;
   --# global in State;
   --  Pointer to data held by buffer Buf

end AIP.Buffers.Data;
