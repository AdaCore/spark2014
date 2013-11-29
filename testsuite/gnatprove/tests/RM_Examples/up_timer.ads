-- The up-time timer is updated once a second
package Up_Timer
  with SPARK_Mode
is
   type Time_Register is limited private;
   type Times is range 0 .. 2**63 - 1;

   procedure Inc (Up_Time : in out Time_Register);

   function Get (Up_Time : Time_Register) return Times;

private
   type Time_Register is record
      Time : Times := 0;
   end record;
end Up_Timer;
