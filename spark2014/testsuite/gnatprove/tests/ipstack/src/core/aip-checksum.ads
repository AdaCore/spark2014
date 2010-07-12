------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP checksum
--  http://www.ietf.org/rfc/rfc1071.txt

package AIP.Checksum is

   function Checksum
     (Packet  : IPTR_T;
      Length  : Natural;
      Initial : M16_T := 0) return M16_T;
   --  Compute IP checksum (1's complement sum of all items in Packet).
   --  Initial is previous checksum, for the case of computing checksum of a
   --  packet split in multiple chunks.

end AIP.Checksum;
