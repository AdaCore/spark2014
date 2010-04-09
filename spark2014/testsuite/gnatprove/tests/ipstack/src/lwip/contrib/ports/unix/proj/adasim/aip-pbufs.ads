------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Pbufs is

   subtype Pbuf_Id is AIP.IPTR_T;
   NOPBUF : constant Pbuf_Id := AIP.NULID;

   function Pbuf_Tlen (Pb : Pbuf_Id) return AIP.U16_T;
   function Pbuf_Len (Pb : Pbuf_Id) return AIP.U16_T;
   function Pbuf_Next (Pb : Pbuf_Id) return Pbuf_Id;

   function Pbuf_Payload (Pb : Pbuf_Id) return AIP.IPTR_T;

   function Pbuf_Free (Pb : Pbuf_Id) return AIP.U8_T;
   procedure Pbuf_Blind_Free (Pb : Pbuf_Id);

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   procedure Pbuf_Ref (Pb : Pbuf_Id);
private

   pragma Import (C, Pbuf_Free, "pbuf_free");
   pragma Import (C, Pbuf_Chain, "pbuf_chain");
   pragma Import (C, Pbuf_Ref, "pbuf_ref");

   pragma Import (C, Pbuf_Next, "pbuf_next_w");
   pragma Import (C, Pbuf_Len, "pbuf_len_w");
   pragma Import (C, Pbuf_Tlen, "pbuf_tot_len_w");
   pragma Import (C, Pbuf_Payload, "pbuf_payload_w");

end AIP.Pbufs;
