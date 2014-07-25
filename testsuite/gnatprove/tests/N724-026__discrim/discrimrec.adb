package body DiscrimRec
  with SPARK_Mode
is

   subtype Register_Bit_64 is Register_Type(Bit_64);
   subtype Register_Bit_32 is Register_Type(Bit_32);

   function Convert_Bit_64_To_Bit_32 (Reg : Register_Bit_64) return Register_Bit_32 is
      (Register_Bit_32'(Option => Bit_32,
                        Ignore_32a => 0,
                        Value_32 => Unsigned_32 (Reg.Value_64 mod 2**32)));

   procedure Test_Register is
      EAX : Register_Type(Option => Bit_32);
   begin
      RAX := (Option => Bit_64, Value_64 => 16);
      EAX := Convert_Bit_64_To_Bit_32 (RAX);
      if (EAX.Value_32 = 16) then
         RAX := (Option => Bit_64, Value_64 => 32);
      end if;
   end Test_Register;

end DiscrimRec;
