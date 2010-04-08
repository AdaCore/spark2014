------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;
with AIP_Pbufs, AIP_IPaddrs, AIP_Ctypes;

package AIP_Netbufs is

   type Netbuf_Id is private;
   NOBUF : constant Netbuf_Id;

   procedure Netbuf_Delete (NB : Netbuf_Id);
   procedure Netbuf_Data
     (NB : Netbuf_Id;
      Data : out System.Address;
      Len : out AIP_Ctypes.U16_T);

   function Netbuf_Next (NB : Netbuf_Id) return AIP_Ctypes.S8_T;

   function Netbuf_Fromaddr (NB : Netbuf_Id) return AIP_IPaddrs.IPaddr_Id;
   function Netbuf_Fromport (NB : Netbuf_Id) return AIP_Ctypes.U16_T;

private

   type Netbuf is record
      P, Ptr : AIP_Pbufs.Pbuf_Id;
      Addr : AIP_IPaddrs.IPaddr_Id;
      Port : AIP_Ctypes.U16_T;
   end record;

   type Netbuf_Id is access all Netbuf;
   NOBUF : constant Netbuf_Id := null;

   pragma Import (C, Netbuf_Delete, "netbuf_delete");
   pragma Import (C, Netbuf_Data, "netbuf_data");
   pragma Import (C, Netbuf_Next, "netbuf_next");

end AIP_Netbufs;
