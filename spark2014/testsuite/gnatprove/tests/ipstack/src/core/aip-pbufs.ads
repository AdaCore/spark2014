------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

-- Packet Buffers (network packet data containers) management.

with AIP.Pools;
--# inherit AIP.Pools;

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
   --# accept W, 3, "Pragma - ignored by the SPARK Examiner";
   pragma Convention (C, Pbuf_Layer);
   --# end accept;

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
   --# accept W, 3, "Pragma - ignored by the SPARK Examiner";
   pragma Convention (C, Pbuf_Kind);
   --# end accept;

   procedure Pbuf_Alloc
     (Layer : Pbuf_Layer;
      Size  : AIP.U16_T;
      Kind  : Pbuf_Kind;
      Pbuf  : out Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Allocate and return a new pbuf of kind KIND, aimed at holding or
   --  referencing SIZE bytes of data plus protocol headers required for
   --  LAYER.
   pragma Import (C, Pbuf_Alloc, "pbuf_alloc_w");

   ---------------------------
   -- Pbuf struct accessors --
   ---------------------------

   function Pbuf_Len (Pb : Pbuf_Id) return AIP.U16_T;
   --# global in Pools.PBUF_POOL;
   --  Amount of packet data held in pbuf PB alone
   pragma Import (C, Pbuf_Len, "pbuf_len_w");

   function Pbuf_Tlen (Pb : Pbuf_Id) return AIP.U16_T;
   --# global in Pools.PBUF_POOL;
   --  Amount of packet data held from pbuf PB to the end of the chain for
   --  this packet. Tlen = Len means PB is the last buffer in the chain for a
   --  packet.
   pragma Import (C, Pbuf_Tlen, "pbuf_tot_len_w");

   function Pbuf_Next (Pb : Pbuf_Id) return Pbuf_Id;
   --# global in Pools.PBUF_POOL;
   --  Pbuf following PB in a chain, either next pbuf for the same packet
   --  or first pbuf of another one.
   pragma Import (C, Pbuf_Next, "pbuf_next_w");

   function Pbuf_Payload (Pb : Pbuf_Id) return AIP.IPTR_T;
   --# global in Pools.PBUF_POOL;
   --  Pointer to Data held or referenced by pbuf PB.
   pragma Import (C, Pbuf_Payload, "pbuf_payload_w");

   --------------------------------
   -- Pbuf reference and release --
   --------------------------------

   procedure Pbuf_Ref (Pb : Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Increase reference count of pbuf PB, with influence on Pbuf_Free
   pragma Import (C, Pbuf_Ref, "pbuf_ref");

   procedure Pbuf_Free (Pb : Pbuf_Id; N_Deallocs : out AIP.U8_T);
   --# global in out Pools.PBUF_POOL;
   --  Decrement PB's reference count, and deallocate if the count reaches
   --  zero. In the latter case, repeat for the following pbufs in a chain for
   --  the same packet. Return the number of pbufs that were de-allocated.
   --
   --  1->2->3 yields ...1->3
   --  3->3->3 yields 2->3->3
   --  1->1->2 yields ......1
   --  2->1->1 yields 1->1->1
   --  1->1->1 yields .......
   pragma Import (C, Pbuf_Free, "pbuf_free_w");

   procedure Pbuf_Blind_Free (Pb : Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Same as Pbuf_Free, ignoring return value
   pragma Import (C, Pbuf_Blind_Free, "pbuf_free");

   procedure Pbuf_Release (Pb : Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Pbuf_Free on PB until it deallocates.

   ---------------------
   -- Pbuf operations --
   ---------------------

   procedure Pbuf_Cat (Head : Pbuf_Id; Tail : Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Append TAIL at the end of the chain starting at HEAD, taking over
   --  the caller's reference to TAIL.
   pragma Import (C, Pbuf_Cat, "pbuf_cat");

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   --# global in out Pools.PBUF_POOL;
   --  Append TAIL at the end of the chain starting at HEAD, and bump TAIL's
   --  reference count. The caller remains responsible of it's own reference,
   --  in particular wrt release duties.
   pragma Import (C, Pbuf_Chain, "pbuf_chain");

   procedure Pbuf_Header (Pb : Pbuf_Id; Bump : AIP.S16_T);
   --# global in out Pools.PBUF_POOL;
   --  Move the payload pointer of PB by BUMP bytes, signed. Typically used to
   --  reveal or hide protocol headers.
   pragma Import (C, Pbuf_Header, "pbuf_header");

end AIP.Pbufs;
