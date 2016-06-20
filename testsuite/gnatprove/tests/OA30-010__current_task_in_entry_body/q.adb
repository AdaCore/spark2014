package body Q is
   procedure S2 (T : out Task_Id) is
   begin
      T := Current_Task;
   end S2;
begin
   null;
end Q;
