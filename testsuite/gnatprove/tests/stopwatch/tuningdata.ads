with System, Ada.Real_Time;

package TuningData with
  SPARK_Mode
is
   -- priorities
   UserPriority    : constant System.Interrupt_Priority := 31;
   TimerPriority   : constant System.Priority := 15;
   DisplayPriority : constant System.Interrupt_Priority := 31;

   -- task periodicities
   TimerPeriod       : constant Ada.Real_Time.Time_Span :=
     Ada.Real_Time.Milliseconds (1000);
end TuningData;
