------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Conversions;

package body AIP.NIF is

   type NIF_Array is array (Netif_Id) of aliased Netif;

   NIFs : NIF_Array;

   --------------------
   -- Allocate_Netif --
   --------------------

   procedure Allocate_Netif (Nid : out EID) is
   begin
      Nid := IF_NOID;
      for J in NIFs'Range loop
         if NIFs (J).State = Invalid then
            Nid := J;

            --  Mark NIF as allocated

            NIFs (J).State := Down;
            exit;
         end if;
      end loop;
   end Allocate_Netif;

   ---------------
   -- Get_Netif --
   ---------------

   function Get_Netif (Nid : Netif_Id) return IPTR_T is
   begin
      return Conversions.To_IPTR (NIFs (Nid)'Address);
   end Get_Netif;

   ----------------------
   -- Is_Local_Address --
   ----------------------

   function Is_Local_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean
   is
   begin
      return Addr = NIF_IP (Nid);
   end Is_Local_Address;

   --------------------------
   -- Is_Broadcast_Address --
   --------------------------

   function Is_Broadcast_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean
   is
   begin
      return Addr = IPaddrs.IP_ADDR_BCAST
               or else Addr = NIF_Broadcast (Nid);
   end Is_Broadcast_Address;

   -------------------
   -- NIF_Broadcast --
   -------------------

   function NIF_Broadcast (Nid : Netif_Id) return IPaddrs.IPaddr is
   begin
      return NIFs (Nid).Broadcast;
   end NIF_Broadcast;

   ------------
   -- NIF_IP --
   ------------

   function NIF_IP (Nid : Netif_Id) return IPaddrs.IPaddr is
   begin
      return NIFs (Nid).IP;
   end NIF_IP;

   --------------
   -- NIF_Mask --
   --------------

   function NIF_Mask (Nid : Netif_Id) return IPaddrs.IPaddr is
   begin
      return NIFs (Nid).Mask;
   end NIF_Mask;

end AIP.NIF;
