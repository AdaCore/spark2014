------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management.

generic
   Chunk_Size : Positive;  --  Size of an individual chunk
   Chunk_Num  : Positive;  --  Total number of chunks statically allocated
   Buffer_Num : Positive;  --  Total number of buffers statically allocated
   type Element is private;
package AIP.Buffers
--# own State;
is

   subtype Buffer_Id is Positive range 0 .. Buffer_Num;
   subtype Chunk_Length is Positive range 0 .. Chunk_Size;
   subtype Data_Length is Positive range 1 .. Chunk_Size * Chunk_Num;

   NOBUF : constant Buffer_Id := 0;

   --  Network packet data is held in buffers, chained as required when
   --  several buffers are needed for a single packet. Such chaining
   --  capabilities are very useful to allow storage of large data blocks in
   --  possibly smaller buffers allocated in static pools. They also offer
   --  convenient incremental packet construction possibilities, such as
   --  chaining initially separate buffers to make up a single packet,
   --  prepending info ahead exsiting data, ...

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

      REF_BUF,
      --  No buffer data is allocated. Instead, the buffer references the data
      --  (payload) through a reference that needs to be attached explicitely
      --  before use.

      LINK_BUF
      --  Buffer data is allocated from available chunks. A chain is
      --  constructed if a single chunk is not big enough for the intended
      --  buffer size.
     );

   procedure Buffer_Alloc
     (Offset :     Chunk_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding or
   --  referencing Size elements of data

end AIP.Buffers;
