with Tank1; use Tank1;
procedure Main with SPARK_Mode is
begin
   loop
      pragma Assert (Valid_Tank);
   end loop;
end Main;
