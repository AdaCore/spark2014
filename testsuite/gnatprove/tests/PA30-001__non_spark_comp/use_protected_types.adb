with SPARK_Mode_Auto;
with SPARK_Mode_On;
procedure Use_Protected_Types with SPARK_Mode is
   X : Integer;
begin
   X := SPARK_Mode_Auto.P.Get_X;
   X := SPARK_Mode_On.P.Get_X;
   X := SPARK_Mode_Auto.S.Get_X;
   X := SPARK_Mode_On.S.Get_X;
   X := SPARK_Mode_Auto.S2.Get_X;
   X := SPARK_Mode_On.S2.Get_X;
end Use_Protected_Types;
