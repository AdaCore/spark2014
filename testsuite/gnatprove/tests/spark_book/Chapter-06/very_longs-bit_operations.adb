pragma SPARK_Mode(Off);

package body Very_Longs.Bit_Operations is

   function TakeLSB_From16(Value : in Double_Octet) return Octet is
   begin
      return Octet(Value and 16#00FF#);
   end TakeLSB_From16;

end Very_Longs.Bit_Operations;
