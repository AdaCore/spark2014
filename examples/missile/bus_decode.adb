-- Bus message decoder implementation
--
-- $Log: bus_decode.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/02/10 20:25:05  adi
-- Initial revision
--
--
package body Bus_Decode is
   function Decode_Bool8(Word : in Bus.Word) return Bool8
   is
      Answer : Bool8 := Bool8'(others => False);
      Working : Bus.Word;
      Idx : Bit8 := Bit8'first;
   begin
      Working := Word;
      while Working > 0 loop
         --# assert working >= 0 and working <= Bus.Word'Last and
         --# idx >= 1 and idx <= 8;
         Answer(Idx) := (Working mod 2) = 1;
         Working := Working / 2;
         if Idx < Bit8'Last then
            Idx := Bit8'Succ(Idx);
         end if;
      end loop;
      return Answer;
   end Decode_Bool8;

   procedure Decode_Byte2(Word : in Bus.Word;
                          Lo,Hi : out SystemTypes.Byte)
   is
   begin
      --# assert Word >= 0 and Word <= Bus.Word'last;
      Lo := Word mod 256;
      Hi := Word / 256;
   end Decode_Byte2;

end Bus_Decode;
