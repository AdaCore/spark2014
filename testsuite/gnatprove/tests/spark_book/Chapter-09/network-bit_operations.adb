pragma SPARK_Mode(Off);
package body Network.Bit_Operations is

   function Shift_Right (Value : in Double_Octet;
                         Count : in Natural) return Double_Octet
     with
       Import     => True,
       Convention => Intrinsic;

   function TakeLSB_From16 (Value : in Double_Octet) return Octet is
   begin
      return Octet (Value and 16#00FF#);
   end TakeLSB_From16;

   function TakeMSB_From16 (Value : in Double_Octet) return Octet is
   begin
      return Octet (Shift_Right (Value, 8));
   end TakeMSB_From16;

end Network.Bit_Operations;
