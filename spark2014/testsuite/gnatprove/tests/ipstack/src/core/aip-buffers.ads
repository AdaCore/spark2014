------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management

--# inherit AIP,  --  Needed in order to inherit AIP.Buffers in child packages
--#         AIP.Support, AIP.Conversions;  --  Needed by child packages

package AIP.Buffers
--# own State;
is
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

   --  'Data' buffers are those buffers holding data.
   --  'No-data' buffers are those buffers referencing external data.

   --  Data_Buffer_Size, Data_Buffer_Num, No_Data_Buffer_Num and Elem can be
   --  changed according to specific project needs. None of these positive
   --  constants should be zero.

   --  These should be defined in AIP.Config???

   Data_Buffer_Size   : constant AIP.U16_T := 256;
   --  Size of an individual data buffer

   Data_Buffer_Num    : constant AIP.U16_T := 10;
   --  Total number of data buffers statically allocated

   No_Data_Buffer_Num : constant AIP.U16_T := 64;
   --  Total number of no-data buffers statically allocated

   --  Type of data element
   subtype Elem is Character;

   subtype Buffer_Length is AIP.U16_T range 0 .. Data_Buffer_Size;

   subtype Data_Length   is AIP.U16_T;
   --  Type Data_Length is used for total length of buffers, both for data
   --  buffers and no-data buffers. Hence it is not necessarily bounded by
   --  the maximal size for data buffers: Data_Buffer_Size * Data_Buffer_Num.

   Buffer_Num : constant AIP.U16_T := Data_Buffer_Num + No_Data_Buffer_Num;
   --  Total number of buffers statically allocated

   subtype Buffer_Id     is AIP.U16_T range 0 .. Buffer_Num;
   subtype Buffer_Index  is AIP.U16_T range 1 .. Buffer_Num;

   NOBUF : constant Buffer_Id := 0;

   ---------------------------
   -- Global initialization --
   ---------------------------

   procedure Buffer_Init;
   --# global out State;
   --  Initialize all arrays of buffers to form initial singly linked
   --  free-lists and set the head of the free-lists

   -----------------------
   -- Buffer allocation --
   -----------------------

   --  Buffers always materialize as a least control structure and can be used
   --  to hold or designate different kinds of data locations.

   type Buffer_Kind is
     (MONO_BUF,
      --  Buffer data is allocated as contiguous chunks. If more than one
      --  buffer is needed, a chain is constructed with contiguous buffers,
      --  so that the data can be moved as if from a single buffer.

      LINK_BUF,
      --  Buffer data is allocated from available chunks. A chain is
      --  constructed if a single chunk is not big enough for the intended
      --  buffer size.

      REF_BUF
      --  No buffer data is allocated. Instead, the buffer references the data
      --  (payload) through a reference that needs to be attached explicitely
      --  before use.
     );
   pragma Convention (C, Buffer_Kind);

   subtype Data_Buffer_Kind is Buffer_Kind range MONO_BUF .. LINK_BUF;

   procedure Buffer_Alloc
     (Offset :     Buffer_Length;
      Size   :     Data_Length;
      Kind   :     Buffer_Kind;
      Buf    : out Buffer_Id);
   pragma Export (C, Buffer_Alloc, "AIP_buffer_alloc");
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding or
   --  referencing Size elements of data starting at offset Offset.

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   --  Note: Buffer_Len and Buffer_Tlen names are too close. We should rename
   --        them after reimplementing the rest of the TCP/IP stack.

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T;
   pragma Export (C, Buffer_Len, "AIP_buffer_len");
   --# global in State;
   --  Amount of packet data
   --  - held in the first chunk of buffer Buf for Kind = LINK_BUF
   --  - held in all chunks of buffer Buf for Kind = MONO_BUF
   --  - referenced by buffer Buf for Kind = REF_BUF

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T;
   pragma Export (C, Buffer_Tlen, "AIP_buffer_tlen");
   --# global in State;
   --  Amount of packet data
   --  - held in all chunks of buffer Buf through the chain for Kind /= REF_BUF
   --    Tlen = Len means Buf is the last buffer in the chain for a packet.
   --  - referenced by buffer Buf for Kind = REF_BUF
   --    Tlen = Len is an invariant in this case.

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id;
   pragma Export (C, Buffer_Next, "AIP_buffer_next");
   --# global in State;
   --  Buffer following Buf in a chain, either next buffer for the same packet
   --  or first buffer of another one, or NOBUF

   function Buffer_Payload (Buf : Buffer_Id) return AIP.IPTR_T;
   pragma Export (C, Buffer_Payload, "AIP_buffer_payload");
   --# global in State;
   --  Pointer to data held or referenced by buffer Buf

   ----------------------------------
   -- Buffer reference and release --
   ----------------------------------

   procedure Buffer_Ref (Buf : Buffer_Id);
   --# global in out State;
   --  Increase reference count of Buffer Buf, with influence on Buffer_Free

   procedure Buffer_Free (Buf : Buffer_Id; N_Deallocs : out AIP.U8_T);
   --# global in out State;
   --  Decrement Buf's reference count, and deallocate if the count reaches
   --  zero. In the latter case, repeat for the following buffers in a chain
   --  for the same packet. Return the number of buffers that were de-allocated
   --
   --  1->2->3 yields ...1->3
   --  3->3->3 yields 2->3->3
   --  1->1->2 yields ......1
   --  2->1->1 yields 1->1->1
   --  1->1->1 yields .......

   procedure Buffer_Blind_Free (Buf : Buffer_Id);
   pragma Export (C, Buffer_Blind_Free, "AIP_buffer_blind_free");
   --# global in out State;
   --  Same as Buffer_Free, ignoring return value

   procedure Buffer_Release (Buf : Buffer_Id);
   --# global in out State;
   --  Buffer_Free on Buf until it deallocates

   -----------------------
   -- Buffer operations --
   -----------------------

   procedure Buffer_Cat (Head : Buffer_Id; Tail : Buffer_Id);
   --# global in out State;
   --  Append Tail at the end of the chain starting at Head, taking over
   --  the caller's reference to Tail

   procedure Buffer_Chain (Head : Buffer_Id; Tail : Buffer_Id);
   --# global in out State;
   --  Append Tail at the end of the chain starting at Head, and bump Tail's
   --  reference count. The caller remains responsible of its own reference,
   --  in particular wrt release duties.

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : out AIP.Err_T);
   pragma Export (C, Buffer_Header, "AIP_buffer_header");
   --# global in out State;
   --  Move the payload pointer of Buf by Bump elements, signed.
   --  Typically used to reveal or hide protocol headers.

   --  Note: if this procedure is called on a buffer not in front of a chain,
   --        then if will result in a violation of the invariant for the total
   --        length of buffers that precede it in the chain.
   --        This means that we should probably change this functionality in
   --        our implementation of LWIP in SPARK.

private

   function Is_Data_Buffer (Buf : Buffer_Id) return Boolean;
   --  Return whether buffer Buf is a data buffer or a no-data buffer.
   --  Declared in the private part as SPARK forbids declarations in body and
   --  style checks require a declaration.

end AIP.Buffers;
