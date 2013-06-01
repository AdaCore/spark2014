package body Modular
is
   type Unsigned_Byte is mod 2 ** 8;

   function Add_Byte_C (A, B : in Integer)
                       return Unsigned_Byte
      with Post    => Add_Byte_C'Result = Unsigned_Byte ((A + B) mod 256)
   is
   begin
      return Unsigned_Byte ((A mod 256 + B mod 256) mod 256);
   end Add_Byte_C;
end Modular;
