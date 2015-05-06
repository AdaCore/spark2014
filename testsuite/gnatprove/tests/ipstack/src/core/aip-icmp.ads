------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Callback oriented low level access to the ICMP services.

with AIP.Buffers;
with AIP.NIF;

package AIP.ICMP is

   -----------------------
   -- IPstack interface --
   -----------------------

   procedure ICMP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --  Process received ICMP packed in Buf
   with
     Global => null,
     Depends => (null => (Buf, Netif));

   procedure ICMP_Reject
     (IP_Buf : Buffers.Buffer_Id;
      I_Type : AIP.U8_T;
      Code   : AIP.U8_T)
   --  Build and send an ICMP rejection message with the specified type and
   --  code for the IP packet in Buf.
   with
     Global  => null,
     Depends => (null => (IP_Buf, I_Type, Code));

end AIP.ICMP;
