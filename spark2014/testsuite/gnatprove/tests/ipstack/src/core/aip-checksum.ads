------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP checksum
--  http://www.ietf.org/rfc/rfc1071.txt

with System;

--# inherit System, AIP;

package AIP.Checksum is

   function Sum
     (Packet  : System.Address;
      Length  : Natural;
      Initial : AIP.M16_T) return AIP.M16_T;
   --  Compute IP checksum (1's complement sum of all items in Packet).
   --  Initial is previous checksum, for the case of computing checksum of a
   --  packet split in multiple chunks. Should be set to 0 on the first call.

end AIP.Checksum;
