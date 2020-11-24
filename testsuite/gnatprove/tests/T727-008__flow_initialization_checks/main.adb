with My_Package; use My_Package;
procedure Main with SPARK_Mode is
begin
      My_Proc;
      pragma Assert (My_Int = 1);
end Main;
