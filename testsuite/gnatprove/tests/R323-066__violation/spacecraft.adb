pragma Ada_2012;

package body Spacecraft
  with SPARK_Mode => On
is

   function Velocity(SatelliteRec: Satellite) return DKFloat
   is
      Distance_Travelled: DKFloat;
   begin
      Distance_Travelled      := SatelliteRec.Revolutions * 2.0 * Pi * SatelliteRec.Altitude;
      return Distance_Travelled / SatelliteRec.Time;
   end Velocity;

end Spacecraft;
