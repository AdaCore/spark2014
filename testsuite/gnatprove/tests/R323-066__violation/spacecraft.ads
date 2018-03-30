with Ada.Numerics; use Ada.Numerics;

package Spacecraft
  with SPARK_Mode => On
is
   type DKFloat is digits 16;
   --subtype DKTime is DKFloat with Dynamic_Predicate => DKTime > 0.0;
   --subtype DKTime is DKFloat range DKFloat'Succ(0.0)..DKFloat'Last;
   subtype DKTime is DKFloat range 1.0..DKFloat'Last;

   type Satellite is private;

   --function Is_Valid_Satellite(SatelliteRec: Satellite) return Boolean;--SatelliteRec.Time /= 0.0
   function Velocity (SatelliteRec: Satellite) return DKFloat;
   --  with
   --Pre => (Is_Valid_Satellite(SatelliteRec));

private
   type Satellite is record
      Time:        DKTime;
      Revolutions: DKFloat;
      Altitude:    DKFloat;
   end record
   with Dynamic_Predicate => (Satellite.Revolutions * 2.0 * Pi * Satellite.Altitude < DKFloat'Last);

   --function Is_Valid_Satellite(SatelliteRec: Satellite) return Boolean is (SatelliteRec.Time /= 0.0);
end Spacecraft;
