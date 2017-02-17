pragma SPARK_Mode(On);

package Very_Longs is

   -- Here "Digit" means a base 256 digit.
   Maximum_Length : constant := 2**16;
   type    Digit_Count_Type is new Natural range 0 .. Maximum_Length;
   subtype Digit_Index_Type is Digit_Count_Type range 1 .. Digit_Count_Type'Last;
   type    Very_Long (Length : Digit_Index_Type) is private;

   -- Constructors.
   function Make_From_Natural (Number : in Natural;
                               Length : in Digit_Index_Type) return Very_Long
      with Post => Make_From_Natural'Result.Length = Length;

   procedure Make_From_Hex_String (Number : in  String;
                                   Result : out Very_Long;
                                   Valid  : out Boolean)
      with
         Depends => ((Result, Valid) => (Number, Result)),
         Pre => Number'Length = 2*Result.Length;

   -- Relational operators. Only Very_Longs of equal size can be compared.
   function "<" (L, R : in Very_Long) return Boolean
      with Pre => L.Length = R.Length;

   function "<=" (L, R : in Very_Long) return Boolean
      with Pre => L.Length = R.Length;

   function ">" (L, R : in Very_Long) return Boolean
      with Pre => L.Length = R.Length;

   function ">=" (L, R : in Very_Long) return Boolean
     with Pre => L.Length = R.Length;

   -- Returns True if Number is zero.
   function Is_Zero (Number : in Very_Long) return Boolean;

   -- Returns the number of significant digits in Number.
   function Number_Of_Digits(Number : in Very_Long) return Digit_Count_Type;

   -- Modular addition (modulo 256**Length).
   function ModAdd (L, R : in Very_Long) return Very_Long
      with
         Pre  => L.Length = R.Length,
         Post => ModAdd'Result.Length = L.Length;

   -- Modular subtraction (modulo 256**Length).
   function ModSubtract (L, R : in Very_Long) return Very_Long
      with
         Pre  => L.Length = R.Length,
         Post => ModSubtract'Result.Length = L.Length;

   -- Modular multiplication (modulo 256**Length).
   function ModMultiply (L, R : in Very_Long) return Very_Long
      with
         Pre  => L.Length = R.Length,
         Post => ModMultiply'Result.Length = L.Length;

   -- Ordinary multiplication.
   function "*" (L, R : in Very_Long) return Very_Long
     with Post => "*"'Result.Length = L.Length + R.Length;

   -- Division returns quotient and remainder.
   procedure Divide (Dividend  : in  Very_Long;
                     Divisor   : in  Very_Long;
                     Quotient  : out Very_Long;
                     Remainder : out Very_Long)
      with
         Depends => (Quotient  =>+ (Dividend, Divisor),
                     Remainder =>+ (Dividend, Divisor)),
         Pre => (Number_Of_Digits (Divisor) > 1)     and
                (Divisor.Length  = Remainder.Length) and
                (Dividend.Length = Quotient.Length ) and
                (Dividend.Length = 2*Divisor.Length);

private
   type Octet        is mod 2**8;
   type Double_Octet is mod 2**16;

   type Digits_Array_Type is array (Digit_Index_Type range <>) of Octet;

   -- The bytes are stored in little endian order.
   type Very_Long (Length : Digit_Index_Type) is
      record
         Long_Digits : Digits_Array_Type (1 .. Length);
      end record;

   function Is_Zero (Number : in Very_Long) return Boolean is
     (for all J in Number.Long_Digits'Range => Number.Long_Digits (J) = 0);

end Very_Longs;
