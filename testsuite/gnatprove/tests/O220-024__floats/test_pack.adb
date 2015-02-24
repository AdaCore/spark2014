package body Test_Pack
  with SPARK_Mode
is

   procedure PID_Update(Pid : in out PID_Obj; Measured : Float) is
   begin
      Pid.Error := Pid.Desired - Measured;  --  @OVERFLOW_CHECK:FAIL
   end PID_Update;

end Test_Pack;
