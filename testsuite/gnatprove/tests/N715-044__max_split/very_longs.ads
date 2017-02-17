pragma SPARK_Mode(On);

package Very_Longs is
   -- Here "Digit" means a base 256 digit.

   type    Digit_Index_Type is new Positive;
   type    Very_Long(Digit_Length : Digit_Index_Type) is private;
   subtype Bit is Natural range 0 .. 1;
   type    Bit_Index_Type is new Natural;

   -- Constructors.
   function Make_From_Natural(Number : in Natural; Digit_Length : in Digit_Index_Type) return Very_Long
     with Post => Make_From_Natural'Result.Digit_Length = Digit_Length;

private
   type Octet is mod 2**8;
   type Digits_Array_Type is array(Digit_Index_Type range <>) of Octet;

   -- The bytes are stored in little endian order (the LSB is at index position zero).
   type Very_Long(Digit_Length : Digit_Index_Type) is
      record
         Long_Digits : Digits_Array_Type(1 .. Digit_Length);
      end record;

end Very_Longs;
