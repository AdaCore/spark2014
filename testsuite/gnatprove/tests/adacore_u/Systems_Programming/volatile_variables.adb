package body Volatile_Variables
  with SPARK_Mode
is
   procedure Set (X : Integer) is
   begin
      null;
   end Set;

   procedure Read_All is
      Tmp : Integer := 0;
   begin
      Tmp := Tmp + AR;
      Tmp := Tmp + AW;
      EW := Tmp;
      Set (ER);
   end Read_All;

   function Read_ER return Integer is
      Tmp : Integer := ER;
   begin
      return Tmp;
   end Read_ER;

end Volatile_Variables;
