with LSC.Types;
with LSC.Byte_Arrays;

-- @summary
-- Base32 encoder and decoder
package Base32
  with SPARK_Mode
is

   -- Check if a character is in the Base32 alphabet
   -- @param C Character to Check
   -- @return True if C is in [a-zA-Z2-7]
   function Valid_Base32_Character
     (C : Character) return Boolean
   is
     (C in 'a' .. 'z' | 'A' .. 'Z' | '2' .. '7')
         with
           Depends => (Valid_Base32_Character'Result => C);

   -- 8bit unsigned byte
   subtype Byte is LSC.Types.Byte;
   -- Array of bytes
   subtype Buffer is LSC.Byte_Arrays.Byte_Array_Type
     with
       Dynamic_Predicate => Buffer'Length mod 5 = 0;

   -- Base32 string that can only contain [a-zA-Z2-7]
   subtype Base32_String is String
     with
       Dynamic_Predicate =>
         Base32_String'Length mod 8 = 0 and
         (for all C of Base32_String =>
            Valid_Base32_Character (C));

   -- Decode Base32 string into a byte array
   -- @param S Valid Base32 string
   -- @return Decoded byte array
   function Decode (S : Base32_String) return Buffer
     with
       Depends => (Decode'Result => S),
       Pre =>
         S'Length < Integer (Natural'Last / 5) and
         S'Length >= 8,
       Post =>
         Decode'Result'Length = S'Length * 5 / 8;


   -- Encodes a byte array into a Base32 string
   -- @param B byte array
   -- @return Base32 string
   function Encode (B : Buffer) return Base32_String
     with
       Depends => (Encode'Result => B),
       Pre => B'Length < Natural'Last / 8;

   -- Decodes Base32 into ASCII
   -- @param S Base32 string
   -- @return String
   function Decode_String (S : Base32_String) return String
     with
       Depends => (Decode_String'Result => S),
       Pre =>
         S'Length < Natural'Last / 5 and S'Length >= 8;

   -- Encodes an ASCII string into Base32
   -- @param ASCII String
   -- @return Base32 string
   function Encode_String (S : String) return Base32_String
     with
       Depends => (Encode_String'Result => S),
       Pre => S'Length mod 5 = 0 and S'Length < Natural'Last / 8;

end Base32;
