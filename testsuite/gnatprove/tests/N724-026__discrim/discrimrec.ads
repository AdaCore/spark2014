package DiscrimRec
with SPARK_Mode
is
   type Unsigned_64 is mod 2**64;
   type Unsigned_32 is mod 2**32;
   type Unsigned_16 is mod 2**16;
   type Unsigned_8  is mod 2**8;

   type Register_Option is (Bit_64, Bit_32, Bit_16, Bit_8);

   type Register_Type (Option: Register_Option := Register_Option'First) is
      record
         case Option is
            when Bit_64 =>
               Value_64   : Unsigned_64;
            when Bit_32 =>
               Ignore_32a : Unsigned_32;
               Value_32   : Unsigned_32;
            when Bit_16 =>
               Ignore_32b : Unsigned_32;
               Ignore_16a : Unsigned_16;
               Value_16   : Unsigned_16;
            when Bit_8 =>
               Ignore_32c : Unsigned_32;
               Ignore_16b : Unsigned_16;
               Value_High : Unsigned_8;
               Value_Low  : Unsigned_8;
         end case;
      end record;

   RAX : Register_Type(Option => Bit_64);

   procedure Test_Register
     with
       Global => (Output => RAX),
       Post => (RAX.Value_64 = 32);

end DiscrimRec;
