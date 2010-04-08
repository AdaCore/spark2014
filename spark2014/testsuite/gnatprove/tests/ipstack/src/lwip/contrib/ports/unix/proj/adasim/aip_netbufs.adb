------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP_Netbufs is

   function Netbuf_Fromaddr (NB : Netbuf_Id) return AIP_IPaddrs.IPaddr_Id is
   begin
      return NB.Addr;
   end Netbuf_Fromaddr;

   function Netbuf_Fromport (NB : Netbuf_Id) return AIP_Ctypes.U16_T is
   begin
      return NB.Port;
   end Netbuf_Fromport;

end AIP_Netbufs;
