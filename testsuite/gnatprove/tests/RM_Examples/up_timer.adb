package body Up_Timer
  with SPARK_Mode
is
   procedure Inc (Up_Time : in out Time_Register) is
   begin
      -- The up timer is incremented every second.
      -- The system procedures require that the system is rebooted
      -- at least once every three years - as the Timer_Reg is a 64 bit
      -- integer it cannot reach Times'Last before a system reboot.
      pragma Assume (if Times'Last = 2**63 - 1 then Up_Time.Time < Times'Last);

      -- Without the previous assume statement it would not be possible
      -- to prove that the following addition would not overflow.
      Up_Time.Time := Up_Time.Time + 1;
   end Inc;

   function Get (Up_Time : Time_Register) return Times is (Up_Time.Time);
end Up_Timer;
