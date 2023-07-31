package body P with SPARK_Mode is
   procedure Initialize_Empty_Class (R : out Empty'Class) is null;

   procedure Initialize_Normal (R : out Normal) is
   begin
      R.A := 0;
   end Initialize_Normal;

   procedure Initialize_Normal_Class (R : out Normal'Class) is null;

   procedure Initialize_Normal_Private (R: out Normal_And_Private) is
   begin
      R := (0,0);
   end Initialize_Normal_Private;

   procedure Initialize_Normal_Rec_And_Private (R: out Normal_Rec_And_Private)
   is
   begin
      R.A.A := 0;
      R.B := 0;
   end Initialize_Normal_Rec_And_Private;

   procedure Initialize_Private (R : out Private_Only) is
   begin
      R.B := 0;
   end Initialize_Private;

   procedure Initialize_Rec_Class (R : out Rec'Class) is null;

   procedure Raise_Exception (T : in out Natural_And_Rec) is
   begin
      raise My_Exception;
   end Raise_Exception;

   procedure Raise_Exception (T : in out Other_Normal) is
   begin
       raise My_Exception;
   end Raise_Exception;
end P;
