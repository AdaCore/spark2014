package body Foo is

   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 60.0; -- we like to faceplant in HD

   G : constant := 3.711; -- gravitational constant on mars

   subtype Min_Range_T is Float64
     range Float64 (Frame'Last) * (-G) * Frame_Length .. 0.0;
   subtype Max_Range_T is Float64
     range 0.0 .. Float64 (Frame'Last) * G * Frame_Length;

   subtype Ratio_T is Float64 range -1.0 .. 1.0;

   function Low_Bound (N : Frame) return Min_Range_T
   is (Float64 (N) * (-G) * Frame_Length);

   function High_Bound (N : Frame) return Max_Range_T
   is (Float64 (N) * G * Frame_Length);

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
        Post   => Invariant (N + 1, New_Speed)
   is
      pragma Assert (Low_Bound (N) >= Low_Bound (N + 1));
      pragma Assert (High_Bound (N) <= High_Bound (N + 1));
   begin
      New_Speed := Old_Speed + (Factor * G * Frame_Length);
      pragma Assert (New_Speed >= Low_Bound (N + 1));
      pragma Assert (New_Speed <= High_Bound (N + 1));
      Average   := (Old_Speed + New_Speed) / 2.0;
   end Faceplant_On_Mars;

end Foo;
