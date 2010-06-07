------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management.

--# inherit AIP,  --  Needed in order to inherit AIP.Buffers in child packages
--#         AIP.Support;  -- Same reason to inherit AIP.Support

package AIP.Buffers
--# own State;
is
   Chunk_Size : constant Positive := 256;
   --  Size of an individual chunk
   Chunk_Num  : constant Positive := 10;
   --  Total number of chunks statically allocated
   Ref_Num    : constant Positive := 64;
   --  Number of 'ref' buffers statically allocated

   subtype Elem is Character;

   --  There should be at least one buffer per chunk, plus additional buffers
   --  for the case where no data is stored
   Buffer_Num : constant Positive := Chunk_Num + Ref_Num;

   subtype Buffer_Id is Natural range 0 .. Buffer_Num;
   subtype Chunk_Length is Natural range 0 .. Chunk_Size;
   subtype Offset_Length is Natural range 0 .. Chunk_Size - 1;
   subtype Data_Length is Positive range 1 .. Chunk_Size * Chunk_Num;

   NOBUF : constant Buffer_Id := 0;

   --  Network packet data is held in buffers, chained as required when
   --  several buffers are needed for a single packet. Such chaining
   --  capabilities are very useful to allow storage of large data blocks in
   --  possibly smaller buffers allocated in static pools. They also offer
   --  convenient incremental packet construction possibilities, such as
   --  chaining initially separate buffers to make up a single packet,
   --  prepending info ahead of existing data, ...

   --  Several packets, each consisting of one or more buffers, may as well be
   --  chained together as 'packet queues' in some circumstances.

   --  Buffers feature reference counters to facilitate sharing and allow
   --  control over deallocation responsibilities.

   -----------------------
   -- Buffer allocation --
   -----------------------

   --  Buffers always materialize as a least control structure and can be used
   --  to hold or designate different kinds of data locations.

   type Buffer_Kind is
     (MONO_BUF,
      --  Buffer data is allocated as contiguous chunks

      LINK_BUF,
      --  Buffer data is allocated from available chunks. A chain is
      --  constructed if a single chunk is not big enough for the intended
      --  buffer size.

      REF_BUF
      --  No buffer data is allocated. Instead, the buffer references the data
      --  (payload) through a reference that needs to be attached explicitely
      --  before use.
     );

   subtype Data_Buffer_Kind is Buffer_Kind range MONO_BUF .. LINK_BUF;

   procedure Buffer_Alloc
     (Offset :     Offset_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding or
   --  referencing Size elements of data

end AIP.Buffers;
