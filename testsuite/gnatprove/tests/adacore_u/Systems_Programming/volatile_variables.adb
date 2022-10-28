package body Volatile_Variables
  with SPARK_Mode
is
   procedure Set (X : Integer) is
   begin
      null;
   end Set;

   procedure Read_All is
      Tmp    : Integer := 0;
      Val_AW : Integer := AW;
      Val_ER : Integer := ER;
   begin
      Tmp := Tmp + AR;
      Tmp := Tmp + Val_AW;
      EW := Tmp;
      Set (Val_ER);
   end Read_All;

   function Read_ER return Integer is
      Tmp : Integer := ER;
   begin
      return Tmp;
   end Read_ER;

end Volatile_Variables;
