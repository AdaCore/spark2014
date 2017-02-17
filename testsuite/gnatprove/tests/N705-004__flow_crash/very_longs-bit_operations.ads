pragma SPARK_Mode(On);

private package Very_Longs.Bit_Operations is

   -- Returns the least significant byte in a 16 bit value.
   function TakeLSB_From16(Value : in Double_Octet) return Octet
     with
       Inline,
       Global => null;

end Very_Longs.Bit_Operations;
