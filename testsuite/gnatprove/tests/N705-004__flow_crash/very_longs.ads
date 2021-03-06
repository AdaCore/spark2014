pragma SPARK_Mode(On);

package Very_Longs is

   type    Digit_Index_Type is new Positive;
   type    Very_Long(Octet_Length : Digit_Index_Type) is private;
   subtype Bit is Natural range 0..1;
   type    Bit_Index_Type is new Natural;

   -- Constructors.
   function Make_From_Natural(Number : in Natural; Octet_Length : in Digit_Index_Type) return Very_Long
     with
       Post => Make_From_Natural'Result.Octet_Length = Octet_Length;

   procedure Make_From_Hex_String(Number : in String; Result : out Very_Long; Valid : out Boolean)
     with
       -- Depends => (Result => Number, Valid => Number),
       Pre => Number'Length = 2*Result.Octet_Length;

   -- Relational operators. Currently only Very_Longs that are the same size can be compared.
   function "<" (L, R : Very_Long) return Boolean
     with
       Pre  => L.Octet_Length = R.Octet_Length;

   function "<="(L, R : Very_Long) return Boolean
     with
       Pre  => L.Octet_Length = R.Octet_Length;

   function ">" (L, R : Very_Long) return Boolean
     with
       Pre  => L.Octet_Length = R.Octet_Length;

   function ">="(L, R : Very_Long) return Boolean
     with
       Pre  => L.Octet_Length = R.Octet_Length;

   -- Convenience test functions.
   function Is_Zero(Number : Very_Long) return Boolean;

   -- Modular addition (modulo 2**Bit_Length).
   function ModAdd(L, R : Very_Long) return Very_Long
     with
       Pre  => L.Octet_Length = R.Octet_Length,
       Post => ModAdd'Result.Octet_Length = L.Octet_Length;

   -- Modular subtraction (modulo 2**Bit_Length).
   function ModSubtract(L, R : Very_Long) return Very_Long
     with
       Pre  => L.Octet_Length = R.Octet_Length,
       Post => ModSubtract'Result.Octet_Length = L.Octet_Length;

   -- Modular multiplication (modulo 2**Bit_Length).
   function ModMultiply(L, R : Very_Long) return Very_Long
     with
       Pre  => L.Octet_Length = R.Octet_Length,
       Post => ModMultiply'Result.Octet_Length = L.Octet_Length;

   -- Ordinary multiplication.
   function "*"(L, R : Very_Long) return Very_Long
     with
       Post => "*"'Result.Octet_Length = L.Octet_Length + R.Octet_Length;

   -- Division divides a 2*Bit_Length bit value by a Bit_Length bit value to return a 2*Bit_Length bit quotient and a Bit_Length bit remainder.
   procedure Divide(Dividend : in Very_Long; Divisor : in Very_Long; Quotient : out Very_Long; Remainder : out Very_Long)
     with
       -- Depends => ((Quotient, Remainder) => (Dividend, Divisor)),
       Pre     => (not Is_Zero(Divisor)) and
                  (Divisor.Octet_Length  = Remainder.Octet_Length) and
                  (Dividend.Octet_Length = Quotient.Octet_Length ) and
                  (Dividend.Octet_Length = 2*Divisor.Octet_Length);

   -- Bit access.
   function  Get_Bit(Number : in Very_Long;  Bit_Number : in Bit_Index_Type) return Bit;
   procedure Put_Bit(Number : in out Very_Long; Bit_Number : in Bit_Index_Type; Bit_Value : in Bit)
     with
       Depends => (Number =>+ (Bit_Number, Bit_Value));

private
   type Octet is mod 2**8;
   type Double_Octet is mod 2**16;

   type Digits_Array_Type is array(Digit_Index_Type range <>) of Octet;

   -- The bytes are stored in little endian order (the LSB is at index position zero).
   type Very_Long(Octet_Length : Digit_Index_Type) is
      record
         Long_Digits : Digits_Array_Type(1 .. Octet_Length);
      end record;

   function Is_Zero(Number : Very_Long) return Boolean is
     (for all I in Number.Long_Digits'Range => Number.Long_Digits(I) = 0);

end Very_Longs;
