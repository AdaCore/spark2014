with Ada.Unchecked_Conversion;

package UC with SPARK_Mode is

   type NvU1 is mod 2**1 with Size => 1;
   type NvU3 is mod 2**3 with Size => 3;
   type NvU4 is mod 2**4 with Size => 4;
   type NvU8 is mod 2**8 with Size => 8;
   type NvU12 is mod 2**12 with Size => 12;
   type NvU32 is mod 2**32 with Size => 32;

   type REG1 is
      record
         F_Field1    : NvU8;
         F_Field2    : NvU4;
	 F_Padding1  : NvU4;
         F_Field3    : NvU1;
         F_Field4    : NvU3;
	 F_Padding2  : NvU12;
      end record
     with  Size => 32, Object_size => 32, Alignment => 4;

   for REG1 use
      record
         F_Field1 at 0 range 0 .. 7;
         F_Field2 at 0 range 8 .. 11;
         F_Padding1 at 0 range 12 .. 15;
         F_Field3 at 0 range 16 .. 16;
         F_Field4 at 0 range 17 .. 19;
         F_Padding2 at 0 range 20 .. 31;
      end record;

   function UC_REG1 is new Ada.Unchecked_Conversion ( Source => REG1, Target => NvU32 );

   function UC_REG1_Inv is new Ada.Unchecked_Conversion ( Source => NvU32, Target => REG1 );

   procedure Test (Val : REG1);

end UC;
