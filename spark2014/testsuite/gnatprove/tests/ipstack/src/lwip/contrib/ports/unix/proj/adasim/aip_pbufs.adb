------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP_Pbufs is

   function Tot_Len (Pb : Pbuf_Id) return CT.U16_T is
   begin
      return Pb.Tot_Len;
   end Tot_Len;

   function Len (Pb : Pbuf_Id) return CT.U16_T is
   begin
      return Pb.Len;
   end Len;

   function Payload (Pb : Pbuf_Id) return System.Address is
   begin
      return Pb.Payload;
   end Payload;

   function Next (Pb : Pbuf_Id) return Pbuf_Id is
   begin
      return Pb.Next;
   end Next;

   procedure Pbuf_Blind_Free (Pb : Pbuf_Id) is
      N : CT.U8_T;
      pragma Warnings (Off, N);
   begin
      N := Pbuf_Free (Pb);
   end Pbuf_Blind_Free;

end AIP_Pbufs;
