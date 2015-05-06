------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  IP checksum
--  http://www.ietf.org/rfc/rfc1071.txt

with AIP.Buffers;

package AIP.Checksum is

   function Sum
     (Buf    : Buffers.Buffer_Id;
      Length : AIP.U16_T) return AIP.M16_T
   --  Compute IP checksum (1's complement sum of all 16-bit words in the first
   --  Length bytes of Buf.
   with
     Global => Buffers.State;

end AIP.Checksum;
