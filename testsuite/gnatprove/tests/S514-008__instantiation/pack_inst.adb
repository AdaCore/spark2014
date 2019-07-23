with Gen;

procedure Pack_Inst with SPARK_Mode is
begin
   for I in 1 .. 100 loop
      declare
         package Inst is new Gen (Integer);
      begin
         null;
      end;
   end loop;
end Pack_Inst;
