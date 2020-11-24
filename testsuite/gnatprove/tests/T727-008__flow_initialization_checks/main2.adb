with My_Package; use My_Package;
procedure Main2 with SPARK_Mode is
begin
   Set_G;
   pragma Assert (Get_G = 1);
end Main2;
