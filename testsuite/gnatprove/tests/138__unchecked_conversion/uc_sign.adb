pragma Ada_2022;
with Ada.Text_IO; use Ada.Text_IO;

package body UC_Sign with SPARK_Mode is

   procedure Test (Val : Reg) is
      V : NvU32 := UC_Reg( (-1, 3, 0) );
   begin
      Put_Line ("Value = " & V'Img);
      pragma Assert ( V = 15 ) ;
   end;

end UC_Sign;
