------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.ARP is

   ---------------
   -- ARP_Input --
   ---------------

   procedure ARP_Input
     (Nid           : NIF.Netif_Id;
      Netif_Address : IPTR_T;
      Buf           : Buffers.Buffer_Id)
   is
   begin
      --  TBD
      raise Program_Error;
   end ARP_Input;

   ----------------
   -- ARP_Output --
   ----------------

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr)
   is
   begin
      --  TBD
      raise Program_Error;
   end ARP_Output;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id)
   is
   begin
      --  TBD
      raise Program_Error;
   end IP_Input;

end AIP.ARP;
