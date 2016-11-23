--  This is a full fixed version. It should have no undischarged VCs.

package body Attempt_3 is

   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0; -- we like to faceplant in HD

   G : constant := 3.711; -- gravitational constant on mars

   subtype Ratio_T is Float64 range -1.0 .. 1.0;
   subtype Drag_T is Float64 range -64.0 .. 64.0;

   function Low_Bound (N : Frame) return Float64
   is (Float64 (N) * (Drag_T'First - Float64'Ceiling (G * Frame_Length)));

   function High_Bound (N : Frame) return Float64
   is (Float64 (N) * (Drag_T'Last + Float64'Ceiling (G * Frame_Length)));

   function Invariant (N : Frame; Speed : Float64) return Boolean
   is (Speed in Low_Bound (N) .. High_Bound (N));

   procedure Faceplant_On_Mars (N         : Frame;
                                Factor    : Ratio_T;
                                Old_Speed : Float64;
                                New_Speed : out Float64;
                                Average   : out Float64;
                                Distance  : in out Float64)
   with Global => null,
        Pre    => N < Frame'Last and then
                  Invariant (N, Old_Speed),
        Post   => Invariant (N + 1, New_Speed)
   is
   begin
      New_Speed := Old_Speed + (Factor * G * Frame_Length);

      pragma Assert (Factor * G * Frame_Length <= 1.0);
      pragma Assert (New_Speed <= Old_Speed + 1.0);
      pragma Assert (Old_Speed <= High_Bound (N));
      pragma Assert (Old_Speed + 1.0 <= High_Bound (N) + 1.0);
      pragma Assert (New_Speed <= High_Bound(N) + 1.0);

      pragma Assert (Float64(N) * 65.0 + 1.0 <= Float64(N+1) * 65.0);
      pragma Assert (High_Bound(N) + 1.0 <= High_Bound(N+1));
      pragma Assert (New_Speed <= High_Bound(N+1));

      Average   := (Old_Speed + New_Speed) / 2.0;
      Distance  := Distance + Average * Frame_Length;
   end Faceplant_On_Mars;

end Attempt_3;
