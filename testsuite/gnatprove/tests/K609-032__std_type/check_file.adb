with Ada.Text_IO; use Ada.Text_IO;

procedure Check_File (Contents : String) is pragma SPARK_Mode (On);

   Col_Count : Positive_Count := 1;

   procedure Check_End_Of_Line (Expect_End_Of_Page : Boolean) is
   begin
      Col_Count := 1;
   end Check_End_Of_Line;

begin
   null;
end Check_File;
