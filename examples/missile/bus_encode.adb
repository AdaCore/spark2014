-- Bus message encoder implementation
--
-- $Log: bus_encode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/10 20:33:50  adi
-- Initial revision
--
--
package body Bus_Encode is

   function Encode_Bool8(data : in Bus_Decode.Bool8) return Bus.Word
   is
      Word : Bus.Word := 0;
      Value : Bus.Word := 1;
   begin
      for Idx in Bus_Decode.Bit8 loop
         --# assert Word >= 0 and Value >= 1;
         if Data(Idx) then
            Word := Word + Value;
         end if;
         if Value < 128 then
            Value := Value * 2;
         end if;
      end loop;
      return Word;
   end Encode_bool8;

   function Encode_Byte2(Lo, Hi : in SystemTypes.Byte) return Bus.Word
   is
      Value : Bus.Word;
   begin
      Value := Lo + (256 * Hi);
      return Value;
   end Encode_Byte2;

end Bus_Encode;
