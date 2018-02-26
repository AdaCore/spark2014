package rng
with
SPARK_Mode
is

    type U32 is mod 2**32;
    type U08 is mod 2**8;
    type Buffer is array (U32 range <>) of U08;

    procedure func(buf : Buffer)
      with
        Pre => buf'Length <= U32'Last;

end rng;
