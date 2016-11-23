--  This is a fully fixed version, with a more precise invariant. It should
--  have no undischarged VCs.

package body Attempt_4 is

   type Float64 is digits 15;

   type Frame is range 0 .. 25_000;

   Frame_Length : constant := 1.0 / 100.0; -- we like to faceplant in HD

   G : constant := 9.80665; -- gravitational constant on earth (wikipedia)

   subtype Ratio_T is Float64 range -1.0 .. 1.0;
   subtype Drag_T is Float64 range -64.0 .. 64.0;

   --  Note the use of Ceiling here; if we use the "precise" bound then we get
   --  arounding errors for speed around frame 9257.
   Max_Speed_Variance : constant Float64 :=
     Drag_T'Last + Float64'Ceiling (G * Frame_Length);

   function Invariant (N        : Frame;
                       Speed    : Float64;
                       Distance : Float64)
                       return Boolean
   is (Speed in Float64 (N) * (- Max_Speed_Variance)
             .. Float64 (N) * Max_Speed_Variance
         and then
       Distance in Float64 (N) * Float64 (N + 1) * (- Max_Speed_Variance) * 0.5
                .. Float64 (N) * Float64 (N + 1) * Max_Speed_Variance * 0.5);

   procedure Faceplant_On_Earth (N         :        Frame;
                                 Factor    :        Ratio_T;
                                 Speed     : in out Float64;
                                 Distance  : in out Float64;
                                 Average   :    out Float64)
   with Global => null,
        Pre    => N < Frame'Last and then
                  Invariant (N,     Speed, Distance),
        Post   => Invariant (N + 1, Speed, Distance)
   is
      Old_Speed : constant Float64 := Speed;
   begin
      Speed    := Speed + (Factor * G * Frame_Length);
      Average  := (Old_Speed + Speed) / 2.0;
      Distance := Distance + (Average * Frame_Length);
   end Faceplant_On_Earth;

end Attempt_4;
