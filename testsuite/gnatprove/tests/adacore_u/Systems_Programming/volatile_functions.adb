package body Volatile_Functions
  with SPARK_Mode
is
   function Read_Non_Volatile return Integer is
      Tmp1 : Integer := AR;
      Tmp2 : Integer := AW;
      Tmp3 : Integer := EW;
   begin
      return Tmp1 + Tmp2 + Tmp3;
   end Read_Non_Volatile;

   function Read_Volatile return Integer is
      Tmp1 : Integer := AR;
      Tmp2 : Integer := AW;
      Tmp3 : Integer := EW;
   begin
      return Tmp1 + Tmp2 + Tmp3;
   end Read_Volatile;

   function Read_ER return Integer is
      Tmp : Integer := ER;
   begin
      return Tmp;
   end Read_ER;

end Volatile_Functions;
