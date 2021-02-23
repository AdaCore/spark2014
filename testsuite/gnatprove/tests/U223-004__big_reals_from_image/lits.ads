with Ada.Numerics.Big_Numbers.Big_Reals; use Ada.Numerics.Big_Numbers.Big_Reals;
package Lits with
  Ghost,
  SPARK_Mode
is
   c_ok_1 : constant := 1.0E-45;
   v_ok_1 : constant Valid_Big_Real := c_ok_1;
   pragma Assert (v_ok_1 = 1.0E-45);

   c_ok_2 : constant := 1.0E3;
   v_ok_2 : constant Valid_Big_Real := c_ok_2;
   pragma Assert (v_ok_2 = 1000.0);

   v_ok_3 : constant Valid_Big_Real := From_Universal_Image ("1", "1_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000");
   pragma Assert (v_ok_3 = 1.0E-45);

   v_ok_4 : constant Valid_Big_Real := From_Universal_Image ("-1", "1_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000");
   pragma Assert (v_ok_4 = -1.0E-45);

   v_ok_5 : constant Valid_Big_Real := From_Universal_Image ("1", "-1_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000");
   pragma Assert (v_ok_5 = -1.0E-45);

   v_ok_6 : constant Valid_Big_Real := From_Universal_Image ("-1", "-1_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000");
   pragma Assert (v_ok_6 = 1.0E-45);

   --  Not supported yet
   v_bad_1 : constant Valid_Big_Real := From_Universal_Image ("-1", "10#1_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000#");
   pragma Assert (v_bad_1 = -1.0E-45);
   v_bad_2 : constant Valid_Big_Real := From_Universal_Image ("-1", "1E45");
   pragma Assert (v_bad_2 = -1.0E-45);

   v_bad_3 : constant Valid_Big_Real := From_Universal_Image ("-1", "toto"); --@PRECONDITION:FAIL
   v_bad_4 : constant Valid_Big_Real := From_Universal_Image ("-1", "0");    --@DIVISION_CHECK:FAIL
end Lits;
