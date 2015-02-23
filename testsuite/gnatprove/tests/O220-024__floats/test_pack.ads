package Test_Pack
  with SPARK_Mode
is
   type PID_Obj is record
      Desired : Float := 0.0;
      Error : Float := 0.0;
   end record;

   procedure PID_Update(Pid : in out Pid_Obj; Measured : Float) with
     Depends => (Pid => (Pid, Measured)),
     Pre => (if Measured > 0.0 then
               Pid.Desired >= Float'First + Measured
             else
               Pid.Desired <= Float'Last + Measured);
end Test_Pack;
