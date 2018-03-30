package Spacecraft.Ctors
  with SPARK_Mode => On
is
   function Satellite_Params_Valid(Time: DKTime; Revolutions: DKFloat; Altitude: DKFloat) return Boolean;
   function New_Satellite(Time: DKTime; Revolutions: DKFloat; Altitude: DKFloat) return Satellite
     with
       Pre => (Satellite_Params_Valid(Time, Revolutions, Altitude));
private
   function Satellite_Params_Valid(Time: DKTime; Revolutions: DKFloat; Altitude: DKFloat) return Boolean is
      (Revolutions * 2.0 * Pi * Altitude < DKFloat'Last and then (Revolutions * 2.0 * Pi * Altitude) / Time < DKFloat'Last);
end Spacecraft.Ctors;
