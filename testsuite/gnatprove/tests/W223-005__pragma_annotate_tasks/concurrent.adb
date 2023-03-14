package body Concurrent is

   task body Some_Task is
   begin
      loop
         null;
      end loop;
   end Some_Task;

   task body Some_Other_Task is
   begin
      loop
         null;
      end loop;
   end Some_Other_Task;
   
   protected body Some_Protected_Object is
      entry Fake_Entry when True is
      begin
         null;
      end;
   end Some_Protected_Object;

   protected body Some_Other_Protected_Object is
      entry Other_Fake_Entry when True is
      begin
         null;
      end;
      procedure Fake_Init is null;
   end Some_Other_Protected_Object;
   
end Concurrent;
