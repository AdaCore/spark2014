with Network.Bit_Operations;
use  Network.Bit_Operations;
package body Network.Helpers
   with SPARK_Mode=> On
is
   procedure Split16 (Value : in  Double_Octet;
                      MSB   : out Octet;
                      LSB   : out Octet) is
   begin
      MSB := TakeMSB_From16 (Value);
      LSB := TakeLSB_From16 (Value);
   end Split16;
end Network.Helpers;
