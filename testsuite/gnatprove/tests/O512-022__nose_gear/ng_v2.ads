with Interfaces; use Interfaces;

package NG_V2 is

   EstimatedGroundVelocityIsAvailable : Boolean := False;
   EstimatedGroundVelocity : Unsigned_16;

   function DistanceSinceLastClickBeforeLastUpdate return Unsigned_16;
   function TimeSinceLastClickBeforeLastUpdate return Unsigned_16;

   procedure UpdateNGVelocity with
     Post => (if EstimatedGroundVelocityIsAvailable then
                EstimatedGroundVelocity =
                  (DistanceSinceLastClickBeforeLastUpdate * 3600) /
                    TimeSinceLastClickBeforeLastUpdate);
end NG_V2;
