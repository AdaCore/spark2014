pragma Ada_2020;

with Ada.Unchecked_Conversion;
with Ada.Text_IO; use Ada.Text_IO;
with Ada.Float_Text_IO; use Ada.Float_Text_IO;

package body Convert is

   function To_Binary32 is new Ada.Unchecked_Conversion
     (Unsigned_32, Binary32);

   function Floatundisf (V : Unsigned_64) return Binary32 is
      Res_Hi, Res_Mid, Res_Lo : Unsigned_32;
      Res : Binary32;
   begin
      --  Assume IEEE 754 Binary32 format

      --  Set Res_Lo to 2.0**23. The nice property is that the LSB of that
      --  value represents 1, the next bit 2 etc. So adding Res_Lo with an
      --  integer can be done using integer addition.
      Res_Lo := 16#4b000000#;

      pragma Assert (To_Binary32 (Res_Lo) = 2.0**23);

      --  So add the lowest 22 bit of V
      Res_Lo := Res_Lo or Unsigned_32 (V and 16#3f_ffff#);

      pragma Assert (To_Binary32 (Res_Lo) = 2.0**23 +
                       Binary32 (Unsigned_32 (V and 16#3f_ffff#)));

      --  Set Res_Mid to 2.0**45, whose LSB represents 2**22.
      Res_Mid := 16#56000000#;
      Res_Mid := Res_Mid or Unsigned_32 (Shift_Right (V, 22) and 16#3f_ffff#);

      pragma Assert (To_Binary32 (Res_Mid) = 2.0**45 +
                       2.0**22 * Binary32 (Unsigned_32
                         (Shift_Right (V, 22) and 16#3f_ffff#)));

      --  Set Res_Hi to 2.0**67, whose LSB represents 2**44.
      Res_Hi := 16#61000000#;
      Res_Hi := Res_Hi or Unsigned_32 (Shift_Right (V, 44) and 16#0f_ffff#);

      pragma Assert (To_Binary32 (Res_Hi) = 2.0**67 +
                       2.0**44 * Binary32 (Unsigned_32
                         (Shift_Right (V, 44) and 16#0f_ffff#)));

      --  Substract implicit ones
      Res := To_Binary32 (Res_Hi) - 2.0**67 - 2.0**45;
      Res := Res + To_Binary32 (Res_Mid) - 2.0**23;
      Res := Res + To_Binary32 (Res_Lo);

      return Res;
   end Floatundisf;

end Convert;
