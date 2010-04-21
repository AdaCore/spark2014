------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

-- Packet Buffer (network data containers) services.

--# inherit AIP;

package AIP.Pbufs is

   subtype Pbuf_Id is AIP.IPTR_T;
   NOPBUF : constant Pbuf_Id := AIP.NULID;

   ---------------------------------
   -- Pbuf allocation and release --
   ---------------------------------

   type Pbuf_Layer is
     (TRANSPORT_PBUF,
      IP_PBUF,
      LINK_PBUF,
      RAW_PBUF);
   pragma Convention (C, Pbuf_Layer);

   type Pbuf_Kind is
     (RAM_PBUF,
      ROM_PBUF,
      REF_PBUF,
      POOL_PBUF);
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

   function Pbuf_Len (Pb : Pbuf_Id) return AIP.U16_T;
   pragma Import (C, Pbuf_Len, "pbuf_len_w");

   function Pbuf_Next (Pb : Pbuf_Id) return Pbuf_Id;
   pragma Import (C, Pbuf_Next, "pbuf_next_w");

   function Pbuf_Payload (Pb : Pbuf_Id) return AIP.IPTR_T;
   pragma Import (C, Pbuf_Payload, "pbuf_payload_w");

   -----------------------------------
   -- Pbuf characteristic accessors --
   -----------------------------------

   procedure Pbuf_Cat (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Cat, "pbuf_cat");

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   pragma Import (C, Pbuf_Chain, "pbuf_chain");

   procedure Pbuf_Ref (Pb : Pbuf_Id);
   pragma Import (C, Pbuf_Ref, "pbuf_ref");

   procedure Pbuf_Header (Pb : Pbuf_Id; Bump : AIP.S16_T);
   pragma Import (C, Pbuf_Header, "pbuf_header");

end AIP.Pbufs;
