package Device_Interfaces is

   type Positive_Float is new Float range 0.0 .. Float'Last;

   Accel  : Positive_Float;
   Giro   : Positive_Float;
   Rotors : Positive_Float;

   function Delta_Change (Rotors1, Rotors2 : Positive_Float) return Boolean is
      (Rotors2 - Rotors1 < 10.0)
   with Pre => Rotors1 <= Rotors2;

end Device_Interfaces;
