pragma SPARK_Mode(On);
private package Network.Bit_Operations is

   -- Returns the least significant byte in a 16 bit value.
   function TakeLSB_From16 (Value : in Double_Octet) return Octet
     with
       Inline => True,
       Global => null;

   -- Returns the most significant by in a 16 bit value.
   function TakeMSB_From16 (Value : Double_Octet) return Octet
     with
       Inline => True,
       Global => null;
end Network.Bit_Operations;
