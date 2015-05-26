package Length_Others
  with SPARK_Mode
is
   type U8 is mod 2 ** 8;
   type Bytes is array (U8 range <>) of Integer;
   procedure Init (S : out Bytes);
end Length_Others;
