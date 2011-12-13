with Ada.Unchecked_Conversion;

package body Ml_Bits
is

   function Buffer_4bit_To_Int32 (X : in T_4bit_Buffer) return T_Int32 is
      Result : T_Int32;
      function Cast_From_4bit is new Ada.Unchecked_Conversion(Source => T_4bit_Buffer, Target => T_4Bit);
   begin
      Result := T_Int32(Cast_From_4bit(X));
      return Result;
   end Buffer_4bit_To_Int32;

end Ml_Bits;
