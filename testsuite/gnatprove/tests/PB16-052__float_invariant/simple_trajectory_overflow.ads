package Simple_Trajectory_Overflow
  with SPARK_Mode
is
   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0;

   G : constant := 9.807; -- gravitational acceleration

   subtype Ratio_T is Float64 range -1.0 .. 1.0;
   subtype Drag_T is Float64 range -64.0 .. 64.0;

   procedure Compute_Speed (Factor    : Ratio_T;
                            Drag      : Drag_T;
                            Old_Speed : Float64;
                            New_Speed : out Float64);

end Simple_Trajectory_Overflow;
