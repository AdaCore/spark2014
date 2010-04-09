------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System, AIP_Ctypes;

package AIP_Pbufs is

   package CT renames AIP_Ctypes;

   type Pbuf_Id is private;
   NOPBUF : constant Pbuf_Id;

   function Tot_Len (Pb : Pbuf_Id) return CT.U16_T;
   function Len (Pb : Pbuf_Id) return CT.U16_T;
   function Next (Pb : Pbuf_Id) return Pbuf_Id;

   function Payload (Pb : Pbuf_Id) return System.Address;

   function Pbuf_Free (Pb : Pbuf_Id) return CT.U8_T;
   procedure Pbuf_Blind_Free (Pb : Pbuf_Id);

   procedure Pbuf_Chain (Head : Pbuf_Id; Tail : Pbuf_Id);
   procedure Pbuf_Ref (Pb : Pbuf_Id);
private

   pragma Import (C, Pbuf_Free, "pbuf_free");
   pragma Import (C, Pbuf_Chain, "pbuf_chain");
   pragma Import (C, Pbuf_Ref, "pbuf_ref");

   type Pbuf;
   type Pbuf_Id is access all Pbuf;

   NOPBUF : constant Pbuf_Id := null;

   type Pbuf_Layer is
     (PBUF_TRANSPORT, PBUF_IP, PBUF_LINK, PBUF_RAW);
   pragma Convention (C, Pbuf_Layer);

   type Pbuf_Kind is
     (PBUF_RAM, PBUF_ROM, PBUF_REF, PBUF_POOL);
   pragma Convention (C, Pbuf_Kind);

   type Pbuf is record
      Next : Pbuf_Id;
      Payload : System.Address;
      Tot_Len : CT.U16_T;
      Len     : CT.U16_T;
      Kind    : Pbuf_Kind;
      Flags   : CT.U8_T;
      Ref     : CT.U16_T;
   end record;

end AIP_Pbufs;
