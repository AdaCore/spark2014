package body System.OS_Interface is

   procedure Alarm_Handler (Interrupt : BB.Interrupt_ID);

   procedure Alarm_Handler (Interrupt : BB.Interrupt_ID) is
   begin
      null;
   end Alarm_Handler;

   procedure Initialize_Timers is
   begin
      BB.Attach_Handler
        (Alarm_Handler'Access,
         Any_Priority'First);
   end Initialize_Timers;

end System.OS_Interface;
