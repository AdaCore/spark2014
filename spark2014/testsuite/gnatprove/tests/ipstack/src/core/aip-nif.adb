------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.NIF is

   type NIF_Array is array (Netif_Id) of Netif;

   NIFs : NIF_Array;

   ----------------------
   -- Is_Local_Address --
   ----------------------

   function Is_Local_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean
   is
   begin
      --  Not implemented???
      raise Program_Error;
      return False;
   end Is_Local_Address;

   --------------------------
   -- Is_Broadcast_Address --
   --------------------------

   function Is_Broadcast_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean
   is
   begin
      --  Not implemented???
      raise Program_Error;
      return False;
   end Is_Broadcast_Address;

------------
   -- NIF_IP --
   ------------

   function NIF_IP (Nid : Netif_Id) return IPaddrs.IPaddr is
   begin
      return NIFs (Nid).IPaddr;
   end NIF_IP;

   --------------
   -- NIF_MASK --
   --------------

   function NIF_MASK (Nid : Netif_Id) return IPaddrs.IPaddr is
   begin
      return NIFs (Nid).Netmask;
   end NIF_MASK;

end AIP.NIF;
