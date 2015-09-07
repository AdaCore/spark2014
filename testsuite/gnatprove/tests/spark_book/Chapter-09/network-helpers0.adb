package body Network.Helpers0
   with SPARK_Mode => On
is

   function Shift_Right (Value : in Double_Octet;
                         Count : in Natural) return Double_Octet
      with Import     => True,
           Convention => Intrinsic;

   procedure Split16 (Value : in  Double_Octet;
                      MSB   : out Octet;
                      LSB   : out Octet) is
   begin
      MSB := Octet (Value and 16#00FF#);
      LSB := Octet (Shift_Right (Value, 8));
   end Split16;
end Network.Helpers0;
