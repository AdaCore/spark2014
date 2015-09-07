private package Network.Helpers
   with SPARK_Mode => On
is
   procedure Split16 (Value : in  Double_Octet;
                      MSB   : out Octet;
                      LSB   : out Octet)
     with
       Global => null,
       Depends => ((MSB, LSB) => Value);
end Network.Helpers;
