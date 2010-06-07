------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management, for
--  buffers holding internally some data

private package AIP.Buffers.Data
--# own State;
is
   --  There is one data buffer per chunk
   Buffer_Num : constant Positive := Chunk_Num;

   subtype Buffer_Id is Natural range 0 .. Buffer_Num;

   -----------------------
   -- Buffer allocation --
   -----------------------

   procedure Buffer_Alloc
     (Offset :     Offset_Length;
      Size   :     Data_Length;
      Kind   :     Data_Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding Size
   --  elements of data

end AIP.Buffers.Data;
