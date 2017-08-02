pragma SPARK_Mode (On);

with Last_Chance_Handler;  pragma Unreferenced (Last_Chance_Handler);
with Count; use Count;

procedure Demo is
  Demo_Counter : Integer := 0;
begin
   loop
     if Demo_Counter > 10 then
       resetCounter(Demo_Counter);
     end if;
     addOne(Demo_Counter);
   end loop;
end Demo;
