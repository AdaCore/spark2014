package Complex_Trajectory
  with SPARK_Mode
is
   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0;

   G : constant := 9.807; -- gravitational acceleration

   subtype Ratio_T is Float64 range -1.0 .. 1.0;
   subtype Drag_T is Float64 range -64.0 .. 64.0;

   Bound : constant Float64 :=
     Drag_T'Last + Float64'Ceiling (G * Frame_Length)
   with Ghost;

   function Low_Bound (N : Frame) return Float64 is (Float64 (N) * (- Bound))
   with Ghost;

   function High_Bound (N : Frame) return Float64 is (Float64 (N) * Bound)
   with Ghost;

   function In_Bounds (V : Float64) return Boolean is
     (V in - Bound * Float64 (Frame'Last) .. Bound * Float64 (Frame'Last))
   with Ghost;

   function Invariant (N        : Frame;
                       Speed    : Float64;
                       Distance : Float64)
                       return Boolean
   is (Speed in Low_Bound (N) .. High_Bound (N)
         and then
       Distance in Float64 (N) * Float64 (N + 1) * (- Bound) * 0.5
                .. Float64 (N) * Float64 (N + 1) * Bound * 0.5)
   with Ghost;

   procedure Compute_Distance (N         :        Frame;
                               Factor    :        Ratio_T;
                               Drag      :        Drag_T;
                               Speed     : in out Float64;
                               Distance  : in out Float64;
                               Average   :    out Float64)
   with Global => null,
        Pre    => N < Frame'Last and then
                  Invariant (N,     Speed, Distance),
        Post   => Invariant (N + 1, Speed, Distance);

end Complex_Trajectory;
