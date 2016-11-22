package body Attempt_1 is

   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0; -- we like to faceplant in HD

   G : constant := 3.711; -- gravitational constant on mars

   subtype Ratio_T is Float64 range -1.0 .. 1.0;

   function Low_Bound (N : Frame) return Float64
   is (Float64 (N) * (-G) * Frame_Length); --@OVERFLOW_CHECK:PASS

   function High_Bound (N : Frame) return Float64
   is (Float64 (N) * G * Frame_Length); --@OVERFLOW_CHECK:PASS

   function Invariant (N : Frame; Speed : Float64) return Boolean
   is (Speed in Low_Bound (N) .. High_Bound (N));

   procedure Faceplant_On_Mars (N         : Frame;
                                Factor    : Ratio_T;
                                Old_Speed : Float64;
                                New_Speed : out Float64;
                                Average   : out Float64)
   with Global => null,
        Pre    => N < Frame'Last and then
                  Invariant (N, Old_Speed),
        Post   => Invariant (N + 1, New_Speed) --@POSTCONDITION:FAIL
   is
   begin
      New_Speed := Old_Speed + (Factor * G * Frame_Length); --@OVERFLOW_CHECK:PASS
      Average   := (Old_Speed + New_Speed) / 2.0;           --@OVERFLOW_CHECK:PASS
   end Faceplant_On_Mars;

end Attempt_1;
