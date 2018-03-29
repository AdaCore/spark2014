package Rchk
with
SPARK_Mode
is

    type U32 is mod 2 ** 32;
    type Buffer is array (U32 range <>) of U32;

    procedure Test (
                    Buf : Buffer;
                    Size : U32
                   );

end Rchk;
