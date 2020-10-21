with Init_Data;
procedure Main_Proc with
  SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := Init_Data.Start_From_Zero;
   Tmp := Init_Data.Start_From_Val;
   Tmp := Init_Data.Start_From_Zero_Bis;
   Tmp := Init_Data.Start_From_Val_Bis;
end Main_Proc;
