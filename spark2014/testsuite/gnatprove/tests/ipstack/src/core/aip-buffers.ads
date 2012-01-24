------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Generic Packet Buffers (network packet data containers) management

with System;
with AIP.Config;

--# inherit AIP,  --  Needed in order to inherit AIP.Buffers in child packages
--#         AIP.Support, AIP.Conversions,
--#         System, AIP.Config;

package AIP.Buffers
--# own State;
is
   pragma Preelaborate;

   --  Network packet data is held in buffers, chained as required when
   --  several buffers are needed for a single packet. Such chaining
   --  capabilities are very useful to allow storage of large data blocks in
   --  possibly smaller buffers allocated in static pools. They also offer
   --  convenient incremental packet construction possibilities, such as
   --  chaining initially separate buffers to make up a single packet,
   --  prepending info ahead of existing data, ...

   --  Buffers feature reference counters to facilitate sharing and allow
   --  control over deallocation responsibilities.

   --  'Data' buffers are those buffers holding data.
   --  'No-data' buffers are those buffers referencing external data.

   --  Buffers always materialize as at least a control structure and can be
   --  used to hold or designate different kinds of data locations.

   type Buffer_Kind is
     (SPLIT_BUF,
      --  Buffer data is possibly allocated in more than one buffer, which
      --  form together a contiguous block of memory. The data can be moved
      --  as if from a single buffer, and the Len field of a split buffer
      --  reflects this by storing the length of the complete chain in the
      --  split buffer.

      LINK_BUF,
      --  Buffer data is allocated from available buffers. A chain is
      --  constructed if a single buffer is not big enough for the intended
      --  buffer size.

      REF_BUF
      --  No buffer data is allocated. Instead, the buffer references the data
      --  (payload) through a reference that needs to be attached explicitely
      --  before use.
     );
   pragma Convention (C, Buffer_Kind);

   --  Despite variations on the underlying data storage scheme, all kinds of
   --  buffer expose a common representation model:

   --  A buffer is a container for data with a start address, a length and
   --  a "payload" pointer, sort of cursor that can be moved back and forth
   --  within the data area (typically to reveal/hide protocol headers as
   --  packet travels within the protocol stack).

   --  Type of data element
   subtype Elem is Character;

   subtype Buffer_Length is AIP.U16_T range 0 .. Config.Data_Buffer_Size;

   subtype Data_Length   is AIP.U16_T;
   --  Type Data_Length is used for total length of buffers, both for data
   --  buffers and no-data buffers. Hence it is not necessarily bounded by
   --  the maximal size for data buffers: Data_Buffer_Size * Data_Buffer_Num.

   Buffer_Num : constant AIP.U16_T :=
                  Config.Data_Buffer_Num + Config.No_Data_Buffer_Num;
   --  Total number of buffers statically allocated

   subtype Buffer_Id is AIP.U16_T range 0 .. Buffer_Num;
   NOBUF : constant := 0;
   --  User exposed buffer identifier, key to all operations on buffers

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

   subtype Data_Buffer_Kind is Buffer_Kind range SPLIT_BUF .. LINK_BUF;

   procedure Buffer_Alloc
     (Offset : Buffer_Length;
      Size   : Data_Length;
      Kind   : Data_Buffer_Kind;
      Buf    : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new Buf of kind Kind, aimed at holding or Size
   --  elements of payload data preceded by Offset bytes of room (initial
   --  payload offset).
   pragma Export (C, Buffer_Alloc, "AIP_buffer_alloc");

   procedure Ref_Buffer_Alloc
     (Offset   : Buffer_Length;
      Size     : Data_Length;
      Data_Ref : System.Address;
      Buf      : out Buffer_Id);
   --# global in out State;
   --  Allocate and return a new REF_BUF Buf, aimed at referencing Size
   --  elements of payload data located at Ref, preceded by Offset bytes of
   --  room (initial payload offset).
   pragma Export (C, Ref_Buffer_Alloc, "AIP_ref_buffer_alloc");

   -----------------------------
   -- Buffer struct accessors --
   -----------------------------

   --  Note: Buffer_Len and Buffer_Tlen names are too close. We should rename
   --        them after reimplementing the rest of the TCP/IP stack.

   function Buffer_Len (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of payload data
   --  - held in buffer Buf for Kind = LINK_BUF
   --  - held in all buffers of the split buffer Buf for Kind = SPLIT_BUF
   --  - referenced by buffer Buf for Kind = REF_BUF
   pragma Export (C, Buffer_Len, "AIP_buffer_len");

   function Buffer_Tlen (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Amount of payload data
   --  - held in all buffers from Buf through the chain for Kind /= REF_BUF
   --    Tlen = Len means Buf is the last buffer in the chain for a packet.
   --  - referenced by buffer Buf for Kind = REF_BUF
   --    Tlen = Len is an invariant in this case.
   pragma Export (C, Buffer_Tlen, "AIP_buffer_tlen");

   function Buffer_Next (Buf : Buffer_Id) return Buffer_Id;
   --# global in State;
   --  Buffer following Buf in a chain, either next buffer for the same packet
   --  or first buffer of another one, or NOBUF
   pragma Export (C, Buffer_Next, "AIP_buffer_next");

   function Buffer_Payload (Buf : Buffer_Id) return System.Address;
   --# global in State;
   --  Pointer to data held or referenced by buffer Buf
   pragma Export (C, Buffer_Payload, "AIP_buffer_payload");

   function Buffer_Poffset (Buf : Buffer_Id) return AIP.U16_T;
   --# global in State;
   --  Room available in BUF in front of payload, typically for
   --  protocol headers

   procedure Buffer_Set_Payload
     (Buf   : Buffer_Id;
      Pload : System.Address;
      Err   : out AIP.Err_T);
   --# global in out State;
   --  Set payload pointer of BUF to PLOAD.
   --
   --  ERR_MEM if PLOAD if off the buffer area.

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
   --# global in out State;
   pragma Export (C, Buffer_Blind_Free, "AIP_buffer_blind_free");
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
   pragma Export (C, Buffer_Cat, "AIP_buffer_cat");

   procedure Buffer_Chain (Head : Buffer_Id; Tail : Buffer_Id);
   --# global in out State;
   --  Append Tail at the end of the chain starting at Head, and bump Tail's
   --  reference count. The caller remains responsible of its own reference,
   --  in particular wrt release duties.

   procedure Buffer_Header
     (Buf  : Buffer_Id;
      Bump : AIP.S16_T;
      Err  : out AIP.Err_T);
   --# global in out State;
   pragma Export (C, Buffer_Header, "AIP_buffer_header");
   --  Move the payload pointer of Buf by Bump elements, signed.  Typically
   --  used to reveal or hide protocol headers. This should only be called on
   --  front buffers (heads of buffer chain). A number of assumed invariants
   --  may break and behavior is undefined otherwise.
   --
   --  ERR_MEM if the requested move would get the payload pointer off the
   --          buffer area.

   procedure Buffer_Copy
     (Dst : Buffer_Id;
      Src : Buffer_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T);
   --# global in out State;
   --  Copy Len bytes from Src's payload into Dst's payload

   ----------------------------
   -- Packet queue structure --
   ----------------------------

   --  A network packet is represented as a chain of buffers. Packets
   --  themselves can be attached to chained lists to form queues.

   --  Separate sets of queues are maintained by each protocol layer. Any
   --  packet can be on a single queue at most at any given time for each layer
   --  but may be on different (unrelated) queues for different layers.

   type Packet_Layer is (Link, Transport);

   type Packet_Queue is private;
   Empty_Packet_Queue : constant Packet_Queue;

   function Head_Packet (Queue : Packet_Queue) return Buffer_Id;
   --  Return head packet of Queue

   function Tail_Packet (Queue : Packet_Queue) return Buffer_Id;
   --  Return tail packet of Queue

   procedure Append_Packet
     (Layer : Packet_Layer;
      Queue : in out Packet_Queue;
      Buf   : Buffer_Id);
   --# global in out State;
   --  Append (push) packet designated by Buf at the tail of Queue

   procedure Remove_Packet
     (Layer : Packet_Layer;
      Queue : in out Packet_Queue;
      Buf   : out Buffer_Id);
   --# global in State;
   --  Detach (pop) head packet from Queue and return its id in Buf

   function Empty (Queue : Packet_Queue) return Boolean;
   --  True if Queue contains no packets

   function Packet_Info (B : Buffer_Id) return System.Address;
   --# global in State;
   procedure Set_Packet_Info (B : Buffer_Id; PI : System.Address);
   --# global in out State;
   --  Get/set layer 3 packet info associated with B

private

   type Packet_Queue is record
      Head, Tail : Buffer_Id;
   end record;

   Empty_Packet_Queue : constant Packet_Queue :=
                         Packet_Queue'(Head => NOBUF, Tail => NOBUF);

   --------------------------------------------------------------
   -- General notes on internal data structures and buffer Ids --
   --------------------------------------------------------------

   --  Each buffer instanciates as a common record associated with a
   --  kind-specific record, all allocated in static arrays in their
   --  respective packages (Buffers.Common, .Data and .No_Data)

   --  Internally, this materializes as two indices for each buffer, the
   --  common array index being exposed to clients. The common indices are
   --  assigned first to Data buffers, then to Ref ones, so we have something
   --  like:

   --  .Data                        .No_Data
   --  data_buf_array [1  ..  D]    ref_buf_array [1 ..  R]
   --                 ----------                  ---------
   --                 |buf_data|                  |buf_ref|
   --
   --        data entries  ref entries
   --                |      |
   --  .Common     vvvvvv  vvvvvvvvv
   --  buf_array [ 1 .. D  D+1.. D+R]
   --            --------------------
   --            |    buf_common    |

   --  We distinguish buffer "Index" subtypes, used as the array range of
   --  valid indices, from buffer "Id" subtypes, used as buffer identifiers
   --  for API purposes. The latter simply feature an extra 0 (NOBUF) in the
   --  range, possible outcome of an allocation attempt for example.

   --  To make sure we perform the necessary common/specific id translations
   --  everywhere needed, we use different types (not subtypes) to manage each
   --  range of indices, so we'll have
   --
   --  Buffer_Id / Buffer_Index for the common blocks,
   --  Rbuf_Id   / Rbuf_Index   for the .No_Data (Reference) specific blocks
   --  Dbuf_Id   / Dbuf_Index   for the .Data specific blocks

   --  We use functions to abstract the common/specific id mapping both ways.

   --  Both the Data and No_Data management units maintain a free list of the
   --  corresponding kinds of buffers. The links are local (kind specific) Id
   --  values stored in the common part of each buffer, using the common
   --  Buffer_Id type.

end AIP.Buffers;
