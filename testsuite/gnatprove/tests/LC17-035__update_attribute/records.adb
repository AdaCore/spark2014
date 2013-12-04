package body Records is
   
   pragma SPARK_Mode (Off);
   
   procedure P1 (R: in out Rec; New_Data: in Integer) is
   begin
      R.S1 := 3;
      R.S2 := New_Data;
      R.S3 := 4;
   end P1;

   procedure P2 (R: in out Rec; New_Data: in Integer) is
   begin
      R.S2 := New_Data;
   end P2;

   procedure P3 (R: in out Rec; New_Data: in Integer; New_Data_2: in My_Range)
   is
   begin
      R := R'Update(S2 => New_Data, S3 => New_Data_2);
   end P3;

   procedure P4 (R: in out Rec; New_Data: in Integer) is
   begin
      R.S1 := 10;
      R.S2 := New_Data;
      R.S3 := 10;
   end P4;

   procedure P5(R: in out Rec) is
   begin
      R.S1 := R.S1 + 1;
      R.S3 := R.S3 + 1;
   end P5;

   procedure P6(R: in out Rec) is
   begin
      R.S1 := R.S1 + 1;
      R.S3 := R.S3 + 1;
   end P6;

   procedure P7 (R: in out Rec) is
   begin
      R.S2 := 5;
   end P7;

   procedure P8 (R: in out Rec) is
   begin
      R.S2 := 5;
   end P8;

end Records;
