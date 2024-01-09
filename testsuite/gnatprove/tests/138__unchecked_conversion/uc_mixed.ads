with Ada.Unchecked_Conversion;

package UC_Mixed with SPARK_Mode is

   type NvU8 is mod 2**8 with Size => 8;

   type REG1 is
      record
         F_Field1    : NvU8;
         F_Field2    : NvU8;
         F_Field3    : NvU8;
         F_Field4    : NvU8;
      end record
     with  Size => 32, Object_size => 32, Alignment => 4;
   for REG1 use
      record
         F_Field1 at 0 range 0 .. 7;
         F_Field2 at 0 range 8 .. 15;
         F_Field3 at 0 range 16 .. 23;
         F_Field4 at 0 range 24 .. 31;
      end record;

    type Buffer is array (1 .. 4) of NvU8;

   function UC_REG1 is new Ada.Unchecked_Conversion ( Source => REG1, Target => Buffer );

   function UC_REG1_Inv is new Ada.Unchecked_Conversion ( Source => Buffer, Target => REG1 );

   procedure Test (Val : REG1);

end uc_mixed;
