------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Netbuf facilities. At this point, we provide straight bindings to the LWIP
--  implementation, with extra _w wrapper functions as needed.


with AIP.IPaddrs;

--# inherit AIP, AIP.IPaddrs;

package AIP.Netbufs is

   subtype Netbuf_Id is AIP.IPTR_T;
   NOBUF : constant Netbuf_Id := AIP.NULID;

   procedure Netbuf_Delete (NB : Netbuf_Id);
   pragma Import (C, Netbuf_Delete, "netbuf_delete");

   procedure Netbuf_Data
     (NB : Netbuf_Id; Data : out AIP.IPTR_T; Len : out AIP.U16_T);
   pragma Import (C, Netbuf_Data, "netbuf_data");

   function Netbuf_Next (NB : Netbuf_Id) return AIP.S8_T;
   pragma Import (C, Netbuf_Next, "netbuf_next");

   function Netbuf_Fromaddr (NB : Netbuf_Id) return IPaddrs.IPaddr_Id;
   pragma Import (C, Netbuf_Fromaddr, "netbuf_fromaddr_w");

   function Netbuf_Fromport (NB : Netbuf_Id) return AIP.U16_T;
   pragma Import (C, Netbuf_Fromport, "netbuf_fromport_w");

end AIP.Netbufs;
