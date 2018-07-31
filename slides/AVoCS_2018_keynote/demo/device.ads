with Device_Interfaces; use Device_Interfaces;

package Device is

   type Mode_T is (Takeoff, Steady_State, Landing, Off);

   procedure Stabilize (Mode    : in Mode_T;
                        Success : out Boolean)
     with Global => (Input  => (Accel, Giro),
                     In_Out => Rotors),
          Pre => Mode /= Off,
          Post => (if Success then
                     Delta_Change (Rotors'Old, Rotors));

   procedure Try_Stabilize (Mode_First : in Mode_T;
                            Mode_Last  : in Mode_T)
   with Pre => Mode_Last /= Off;

end Device;
