with Ada.Text_IO;
package body Test_Inline with SPARK_Mode => On is

   A : Integer := 0;
   B : Integer := 0;

   --  These funcitons simulate reading external sensor values
   function Read_External_A return Integer with Volatile_Function;
   function Read_External_B return Integer with Volatile_Function;

   function Read_External_A return Integer with SPARK_Mode => Off is
   begin
      return 1;
   end Read_External_A;
   function Read_External_B return Integer with SPARK_Mode => Off is
   begin
      return 1;
   end Read_External_B;

   --  store sensor values in package state variables A and B
   procedure Set_A_And_B is
   begin
      A := Read_External_A;
      B := Read_External_B;
   end Set_A_And_B;

   procedure Print_A is
   begin
      Ada.Text_IO.Put_Line (A'Image);
   end Print_A;

   procedure Print_B is
   begin
      Ada.Text_IO.Put_Line (B'Image);
   end Print_B;

   procedure Do_Test_A is
   begin
      Set_A_And_B;
      Print_A;
   end Do_Test_A;

   procedure Do_Test_B is
   begin
      Set_A_And_B;
      Print_B;
   end Do_Test_B;

   procedure Do_Test is
   begin
      Do_Test_A;
      --  gnatprove gives this output for call to Do_Test_A;
      --  test_inline.adb:51:07: warning: unused assignment to "A"
      --  test_inline.adb:51:07: warning: unused assignment to "B"
      Set_A_And_B;
      Print_A;
      Print_B;
   end Do_Test;

end Test_Inline;
