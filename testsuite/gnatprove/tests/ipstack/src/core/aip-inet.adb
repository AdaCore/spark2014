------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Inet is

   --  Amount of room to allocate in a buffer for headers of each broad
   --  protocol layer, each to be accumulated on top of the lower ones.

   LINK_BUF_HLEN      : constant AIP.U16_T := 14;
   --  Ethernet header

   IP_BUF_HLEN        : constant AIP.U16_T := 20;
   --  IP header (assume no options)

   TRANSPORT_BUF_HLEN : constant AIP.U16_T := 20;
   --  TCP header

   -------------
   -- HLEN_To --
   -------------

   function HLEN_To (L : Inet_Layer) return AIP.U16_T is
      Room : AIP.U16_T := 0;
   begin
      if L >= TRANSPORT_LAYER then
         Room := Room + TRANSPORT_BUF_HLEN;
      end if;
      if L >= IP_LAYER then
         Room := Room + IP_BUF_HLEN;
      end if;
      Room := Room + LINK_BUF_HLEN;

      return Room;
   end HLEN_To;

end AIP.Inet;
