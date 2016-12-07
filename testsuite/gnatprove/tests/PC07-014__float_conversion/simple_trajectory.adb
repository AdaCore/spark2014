package body Simple_Trajectory
  with SPARK_Mode
is

   procedure Faceplant_On_Mars (N         : Frame;
                                Factor    : Ratio_T;
                                Old_Speed : Float64;
                                New_Speed : out Float64)
   is
      Delta_Speed : constant Float64 := Factor * G * Frame_Length;
   begin
      New_Speed := Old_Speed + Delta_Speed;

      --  Bound all quantities involved with constants

      pragma Assert (Delta_Speed in -1.0 .. 1.0);
      pragma Assert (In_Bounds (Old_Speed));
      pragma Assert (In_Bounds (High_Bound(N)));
      pragma Assert (In_Bounds (Low_Bound(N)));

      --  Bound New_Speed from above, first by High_Bound(N) + 1.0

      pragma Assert (New_Speed <= Old_Speed + 1.0);
      pragma Assert (Old_Speed <= High_Bound (N));
      pragma Assert (Old_Speed + 1.0 <= High_Bound(N) + 1.0);
      pragma Assert (New_Speed <= High_Bound(N) + 1.0);

      pragma Assert (Float64(N) * 65.0 + 1.0 <= Float64(N+1) * 65.0);

      pragma Assert (High_Bound(N) + 1.0 <= High_Bound(N+1));
      pragma Assert (New_Speed <= High_Bound(N+1));

      --  Bound New_Speed from below, first by Low_Bound(N) - 1.0

      pragma Assert (New_Speed >= Old_Speed - 1.0);
      pragma Assert (Old_Speed >= Low_Bound (N));
      pragma Assert (Old_Speed - 1.0 >= Low_Bound(N) - 1.0);
      pragma Assert (New_Speed >= Low_Bound(N) - 1.0);

      pragma Assert (Float64(N) * (-65.0) - 1.0 >= Float64(N+1) * (-65.0));
      pragma Assert (Low_Bound(N) - 1.0 >= Low_Bound(N+1));
      pragma Assert (New_Speed >= Low_Bound(N+1));

   end Faceplant_On_Mars;

end Simple_Trajectory;
