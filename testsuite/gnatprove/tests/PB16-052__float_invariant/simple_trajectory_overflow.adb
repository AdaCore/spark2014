package body Simple_Trajectory_Overflow
  with SPARK_Mode
is

   procedure Compute_Speed (Factor    : Ratio_T;
                            Drag      : Drag_T;
                            Old_Speed : Float64;
                            New_Speed : out Float64)
   is
      Delta_Speed : constant Float64 := Drag + Factor * G * Frame_Length;
    begin
      New_Speed := Old_Speed + Delta_Speed;
   end Compute_Speed;

end Simple_Trajectory_Overflow;
