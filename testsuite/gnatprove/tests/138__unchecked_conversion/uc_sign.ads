with Ada.Unchecked_Conversion;

package UC_Sign with SPARK_Mode is

   type Int_M2_1 is range -2 .. 1 with Size => 2;
   type Int_M1_1 is range -1 .. 1 with Size => 2;
   type Int_M1_2 is range -1 .. 2 with Size => 2;
   type Int_0_3 is range 0 .. 3 with Size => 2;

   type NvU28 is mod 2**28 with Size => 28;

   type Reg is
      record
         F_Field1 : Int_M2_1;
         F_Field2 : Int_0_3;
	 F_Padding : NvU28;
      end record
   with Size => 32, Object_size => 32, Alignment => 4;

   for Reg use
      record
         F_Field1 at 0 range 0 .. 1;
         F_Field2 at 0 range 2 .. 3;
	 F_Padding at 0 range 4 .. 31;
      end record;

   type NvU32 is mod 2**32;

   function UC_Reg is new Ada.Unchecked_Conversion ( Source => Reg, Target => NvU32 );

   procedure Test (Val : Reg);

end UC_Sign;
