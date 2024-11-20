with Ada.Text_IO;

package body Compressed_Check_For_Uninitialized_Records with SPARK_Mode is

   procedure Initialize is
   begin
      R.A := 1;
   end Initialize;

   procedure Use_Rec is
   begin
      R.B := R.B + 1;
      Ada.Text_IO.Put_Line (Natural'Image(R.B));
   end Use_Rec;

end Compressed_Check_For_Uninitialized_Records;
