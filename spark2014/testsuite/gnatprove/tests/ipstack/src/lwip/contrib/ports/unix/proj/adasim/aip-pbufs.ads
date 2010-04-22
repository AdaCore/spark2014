------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

-- Packet Buffer (network packet data containers) services.

--# inherit AIP;

package AIP.Pbufs is

   subtype Pbuf_Id is AIP.IPTR_T;
   NOPBUF : constant Pbuf_Id := AIP.NULID;

   --  Network packet data is held in buffers, chained as required when
   --  several buffers are needed for a single packet. Such chaining
   --  capabilities are very useful to allow storage of large data blocks in
   --  possibly smaller buffers allocated in static pools. They also offer
   --  convenient incremental packet construction possibilities, such as
   --  chaining initially separate buffers to make up a single packet,
   --  prepending info ahead exsiting data, ...

   --  Several packets, each consisting of one or more buffers, may as well be
   --  chained together as 'packet queues' in some circumstances.

   --  Pbufs feature reference counters to facilitate sharing and allow
   --  control over deallocation responsibilities.

   ---------------------
   -- Pbuf allocation --
   ---------------------

   --  Pbufs may be declared as intended to hold data pertaining to some stack
   --  layer, which causes allocation of extra room for the necessary protocol
   --  headers.

   type Pbuf_Layer is
     (TRANSPORT_PBUF,
      IP_PBUF,
      LINK_PBUF,
      RAW_PBUF);
   pragma Convention (C, Pbuf_Layer);

   --  Pbufs always materialize as a least control structure and can be used
   --  to hold or designate different kinds of data locations.

   type Pbuf_Kind is
     (RAM_PBUF,
      --  Pbuf struct and data (protocol headers included) are allocated as
      --  one single chunk of RAM.

      ROM_PBUF,
      REF_PBUF,
      --  A Pbuf struct alone gets allocated. The data (payload) it "holds"
      --  is a reference that needs to be attached explicitely before use.

      POOL_PBUF
      --  Pbuf struct and data are both allocated from a static pool. A chain
      --  is constructed if a single pbuf is not big enough for the intended
      --  packet size.
     );
   pragma Convention (C, Pbuf_Kind);

   function Pbuf_Alloc
     (Layer : Pbuf_Layer;
      Size  : AIP.U16_T;
      Kind  : Pbuf_Kind) return Pbuf_Id;
   pragma Import (C, Pbuf_Alloc, "pbuf_alloc");
   --  Allocate and return a new pbuf of kind KIND, aimed at holding or
   --  referencing SIZE bytes of data plus protocol headers required for
   --  LAYER.

   ---------------------------
   -- Pbuf struct accessors --
   ---------------------------

   function Pbuf_Len (Pb : Pbuf_Id) return AIP.U16_T;
   pragma Import (C, Pbuf_Len, "pbuf_len_w");
   --  Amount of data held in pbuf PB alone

   function Pbuf_Tlen (Pb : Pbuf_Id) return AIP.U16_T;
   pragma Import (C, Pbuf_Tlen, "pbuf_tot_len_w");
   --  Amount of packet data held from pbuf PB to the end of the chain for
   --  this packet. Tlen = Len means PB is the last buffer in the chain for a
   --  packet.

   function Pbuf_Next (Pb : Pbuf_Id) return Pbuf_Id;
   pragma Import (C, Pbuf_Next, "pbuf_next_w");
   --  Pbuf following PB in a chain, either next pbuf for the same packet
   --  or first pbuf of another one.

   function Pbuf_Payload (Pb : Pbuf_Id) return AIP.IPTR_T;
   pragma Import (C, Pbuf_Payload, "pbuf_payload_w");
   --  Pointer to Data held or referenced by pbuf PB.

   --------------------------------
   -- Pbuf reference and release --
   --------------------------------

   procedure Pbuf_Ref (Pb : Pbuf_Id);
   pragma Import (C, Pbuf_Ref, "pbuf_ref");
   --  Increase reference count of pbuf PB, with influence on Pbuf_Free

   function Pbuf_Free (Pb : Pbuf_Id) return AIP.U8_T;
   pragma Import (C, Pbuf_Free, "pbuf_free");
   --  Decrement PB's reference count, and deallocate if the count reaches
   --  zero. In the latter case, repeat for the following pbufs in a chain for
   --  the same packet. Return the number of pbufs that were de-allocated.
   --
   --  1->2->3 yields ...1->3
   --  3->3->3 yields 2->3->3
   --  1->1->2 yields ......1
   --  2->1->1 yields 1->1->1
   --  1->1->1 yields .......

   procedure Pbuf_Blind_Free (Pb : Pbuf_Id);
   pragma Import (C, Pbuf_Blind_Free, "pbuf_free");
   --  Same as Pbuf_Free, ignoring return value

   ---------------------
   -- Pbuf operations --
   ---------------------

   procedure Pbuf_Cat (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Cat, "pbuf_cat");
   --  Append TAIL at the end of the chain starting at HEAD, taking over
   --  the caller's reference to TAIL.

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Chain, "pbuf_chain");
   --  Append TAIL at the end of the chain starting at HEAD, and bump TAIL's
   --  reference count. The caller remains responsible of it's own reference,
   --  in particular wrt release duties.

   procedure Pbuf_Header (Pb : Pbuf_Id; Bump : AIP.S16_T);
   pragma Import (C, Pbuf_Header, "pbuf_header");
   --  Move the payload pointer of PB by BUMP bytes. Typically used to
   --  reveal or hide protocol headers.

end AIP.Pbufs;
