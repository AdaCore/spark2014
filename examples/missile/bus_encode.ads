-- Bus message encoder
--
-- $Log: bus_encode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/10 20:33:45  adi
-- Initial revision
--
--
with Bus,SystemTypes,Bus_Decode;
--# inherit Bus, SystemTypes, Bus_Decode;
package Bus_Encode is

   function Encode_Bool8(data : in Bus_Decode.Bool8) return Bus.Word;

   function Encode_Byte2(Lo, Hi : in SystemTypes.Byte) return Bus.Word;

end Bus_Encode;
