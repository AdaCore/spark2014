-- Bus message decoder
--
-- $Log: bus_decode.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/10 20:25:01  adi
-- Initial revision
--
--
with Bus,SystemTypes;
--# inherit Bus, SystemTypes;
package Bus_Decode is
   subtype Bit8 is Positive range 1..8;
   type Bool8 is array(Bit8) of Boolean;

   subtype Bit2 is Positive range 1..2;
   type Byte2 is array(Bit2) of SystemTypes.Byte;

   function Decode_Bool8(Word : in Bus.Word) return Bool8;

   procedure Decode_Byte2(Word : in Bus.Word;
                          Lo,Hi : out SystemTypes.Byte);
   --# derives Lo, Hi from Word;

end Bus_Decode;
