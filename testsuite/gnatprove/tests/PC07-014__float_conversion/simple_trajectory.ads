package Simple_Trajectory
  with SPARK_Mode
is
   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0; -- we like to faceplant in HD

   G : constant := 3.711; -- gravitational constant on mars

   subtype Ratio_T is Float64 range -1.0 .. 1.0;
   subtype Drag_T is Float64 range -64.0 .. 64.0;

   function Low_Bound (N : Frame) return Float64 is
     (Float64 (N) * (Drag_T'First - Float64'Ceiling (G * Frame_Length)))
   with Ghost;

   function High_Bound (N : Frame) return Float64 is
     (Float64 (N) * (Drag_T'Last + Float64'Ceiling (G * Frame_Length)))
   with Ghost;

   function Invariant (N : Frame; Speed : Float64) return Boolean is
     (Speed in Low_Bound (N) .. High_Bound (N))
   with Ghost;

   function In_Bounds (V : Float64) return Boolean is
     (V in -65.0 * 25_000.0 .. 65.0 * 25_000.0)
   with Ghost;

   procedure Faceplant_On_Mars (N         : Frame;
                                Factor    : Ratio_T;
                                Old_Speed : Float64;
                                New_Speed : out Float64)
   with Global => null,
        Pre    => N < Frame'Last and then
                  Invariant (N, Old_Speed),
        Post   => Invariant (N + 1, New_Speed);

end Simple_Trajectory;
