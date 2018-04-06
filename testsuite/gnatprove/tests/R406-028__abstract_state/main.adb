with Global_Contracts.Accessors;

procedure Main with SPARK_Mode is
   X : Integer;
begin
   X := Global_Contracts.Accessors.Get_G;
end Main;
