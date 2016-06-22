package body Interrupt_Handler is

   protected body PO is
      procedure P is
      begin
         if True then
            T := Current_Task;
         end if;
      end P;
   end PO;

begin
   null;
end Interrupt_Handler;
