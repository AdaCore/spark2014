with Interfaces; use Interfaces;

package body Simple_Trajectory
  with SPARK_Mode
is

   procedure Compute_Speed (N         : Frame;
                            Factor    : Ratio_T;
                            Drag      : Drag_T;
                            Old_Speed : Float64;
                            New_Speed : out Float64)
   is
      Delta_Speed : constant Float64 := Drag + Factor * G * Frame_Length;
      function T (N : Integer) return Float64 is (Float64 (N)) with Ghost;
      N_Bv : constant Unsigned_16 := Unsigned_16(N) with Ghost;
   begin
      New_Speed := Old_Speed + Delta_Speed;

      --  Bound all quantities involved with constants

      pragma Assert (Delta_Speed in -Bound .. Bound);
      pragma Assert (In_Bounds (High_Bound(N)));
      pragma Assert (In_Bounds (Low_Bound(N)));

      --  Intermediate assertions to bound New_Speed

      pragma Assert (Float64(N_Bv) * Bound + Bound = (Float64(N_Bv) + 1.0) * Bound);
      pragma Assert (Float64(N) * Bound + Bound = (Float64(N) + 1.0) * Bound);
      pragma Assert (Float64(N) * (-Bound) - Bound = (Float64(N) + 1.0) * (-Bound));

      --  Relate the property on Float64(N) + 1.0 to the same property on Float64(N+1)

      pragma Assert (T(1) = 1.0);
      pragma Assert (Float64(N) + 1.0 = Float64(N + 1));

      pragma Assert (New_Speed >= Float64 (N) * (-Bound) - Bound);
      pragma Assert (New_Speed >= Float64 (N + 1) * (-Bound));
      pragma Assert (New_Speed <= Float64 (N) * Bound + Bound);
      pragma Assert (New_Speed <= Float64 (N + 1) * Bound);
   end Compute_Speed;

end Simple_Trajectory;
