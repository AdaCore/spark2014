package body AIP.Net with
  SPARK_Mode
is
   LINK_BUF_HLEN      : constant Integer := 14;
   --  Ethernet header

   IP_BUF_HLEN        : constant Integer := 20;
   --  IP header (assume no options)

   TRANSPORT_BUF_HLEN : constant Integer := 20;
   --  TCP header

   function HLEN_To (L : Integer) return Integer is
      Room : Integer := 0;
   begin
      if L >= 3 then
         Room := Room + TRANSPORT_BUF_HLEN;
      end if;
      if L >= 5 then
         Room := Room + IP_BUF_HLEN;
      end if;
      Room := Room + LINK_BUF_HLEN;

      return Room;
   end HLEN_To;
end AIP.Net;
