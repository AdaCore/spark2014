with Ada.Unchecked_Conversion;

package UC_Array with SPARK_Mode is

   type NvU1 is mod 2**1 with Size => 1;
   type NvU3 is mod 2**3 with Size => 3;
   type NvU4 is mod 2**4 with Size => 4;
   type NvU8 is mod 2**8 with Size => 8;
   type NvU12 is mod 2**12 with Size => 12;
   type NvU32 is mod 2**32 with Size => 32;

   type REG1 is
      array (1 .. 4) of NvU8
     with Size => 32, Object_size => 32, Alignment => 4;

   function UC_REG1 is new Ada.Unchecked_Conversion ( Source => REG1, Target => NvU32 );

   function UC_REG1_Inv is new Ada.Unchecked_Conversion ( Source => NvU32, Target => REG1 );

   procedure Test (Val : REG1);

end UC_Array;
