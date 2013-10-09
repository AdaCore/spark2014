with Interfaces; use Interfaces;

package NG_V1 is

   EstimatedGroundVelocityIsAvailable : Boolean := False;
   EstimatedGroundVelocity : Unsigned_16;

   --  Global data saved between invocations

   WHEEL_DIAMETER : constant := 26;
   WHCF : constant := (((WHEEL_DIAMETER * 254) / 7) * 22) / 100;

   PrevTime : Unsigned_16 := 0;
   PrevCount : Unsigned_16 := 0;
   PrevCurr : Unsigned_16 := 0;
   FirstTime : Unsigned_16 := 0;
   NumFailedUpdates : Unsigned_16 := 0;
   UpdatedWithoutNewClicks : Unsigned_16 := 0;

   CurrTime : Unsigned_16 := 0;
   ThisTime : Unsigned_16 := 0;
   ThisCount : Unsigned_16 := 0;

   function DistanceFromLastClickToLastUpdate return Unsigned_16;

   procedure UpdateNGVelocity with
     Post => (if EstimatedGroundVelocityIsAvailable then
                EstimatedGroundVelocity =
                 (((WHCF * (ThisCount - PrevCount)) +
                    ((WHCF * (ThisCount - PrevCount)) * (CurrTime - ThisTime))
                      / (ThisTime - PrevTime))
                   * 3600) /
                    (CurrTime - PrevTime));
end NG_V1;
