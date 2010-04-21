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
   --  several buffers are needed for a single packet. Chaining capabilities
   --  are very useful to allow storage of large data blocks in possibly
   --  smaller buffers allocated in static pools. They also offer convenient
   --  incremental packet construction possibilities, such as chaining
   --  initially separate buffers to make up a single packet, prepending info
   --  ahead exsiting data, ...

   ---------------------------------
   -- Pbuf allocation and release --
   ---------------------------------

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

   function Pbuf_Free (Pb : Pbuf_Id) return AIP.U8_T;
   pragma Import (C, Pbuf_Free, "pbuf_free");

   procedure Pbuf_Blind_Free (Pb : Pbuf_Id);
   pragma Import (C, Pbuf_Blind_Free, "pbuf_free");

   -----------------------------------
   -- Pbuf characteristic accessors --
   -----------------------------------

   function Pbuf_Tlen (Pb : Pbuf_Id) return AIP.U16_T;
   pragma Import (C, Pbuf_Tlen, "pbuf_tot_len_w");
   --  Amount of packet data held from pbuf PB to the end of the chain it
   --  participates in.

   function Pbuf_Len (Pb : Pbuf_Id) return AIP.U16_T;
   pragma Import (C, Pbuf_Len, "pbuf_len_w");
   --  Amount of data held in pbuf PB. Len = Tlen means PB is the last
   --  buffer in a chain.

   function Pbuf_Next (Pb : Pbuf_Id) return Pbuf_Id;
   pragma Import (C, Pbuf_Next, "pbuf_next_w");
   --  Pbuf following PB in a chain. Note that full *packets*, not only
   --  packet *buffers* may be chained together, so the len/tlen check is
   --  the only proper way to detect the end of a packet.

   function Pbuf_Payload (Pb : Pbuf_Id) return AIP.IPTR_T;
   pragma Import (C, Pbuf_Payload, "pbuf_payload_w");
   --  Pointer to Data held or referenced by pbuf PB.

   ---------------------
   -- Pbuf operations --
   ---------------------

   procedure Pbuf_Cat (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Cat, "pbuf_cat");

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Chain, "pbuf_chain");

   procedure Pbuf_Ref (Pb : Pbuf_Id);
   pragma Import (C, Pbuf_Ref, "pbuf_ref");

   procedure Pbuf_Header (Pb : Pbuf_Id; Bump : AIP.S16_T);
   pragma Import (C, Pbuf_Header, "pbuf_header");

end AIP.Pbufs;
