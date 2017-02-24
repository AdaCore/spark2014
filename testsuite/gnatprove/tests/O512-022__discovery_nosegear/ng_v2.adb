package body NG_V2 is

   --  Interface to sensors

   function Millisecs return Unsigned_16;
   pragma Import (C, Millisecs);

   function NGClickTime return Unsigned_16;
   pragma Import (C, NGClickTime);

   function NGRotations return Unsigned_16;
   pragma Import (C, NGRotations);

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

   --  API

   function DistanceSinceLastUpdate return Unsigned_16 with
     Pre => ThisTime /= PrevTime;

   function TimeFromLastClickToLastUpdate return Unsigned_16 is
      (ThisTime - PrevTime);

   function TimeSinceLastUpdate return Unsigned_16 is
      (CurrTime - ThisTime);

   function TimeSinceLastClickBeforeLastUpdate return Unsigned_16 is
      (TimeFromLastClickToLastUpdate + TimeSinceLastUpdate);

   function DistanceFromLastClickToLastUpdate return Unsigned_16 is
      (WHCF * (ThisCount - PrevCount));

   function DistanceSinceLastUpdate return Unsigned_16 is
      (DistanceFromLastClickToLastUpdate * TimeSinceLastUpdate)
        / TimeFromLastClickToLastUpdate;

   function DistanceSinceLastClickBeforeLastUpdate return Unsigned_16 is
      (DistanceFromLastClickToLastUpdate + DistanceSinceLastUpdate);

   procedure UpdateNGVelocity is
      T1, T2, D1, D2 : Unsigned_16;
   begin
      if ThisTime = PrevTime then
	 EstimatedGroundVelocityIsAvailable := False;
	 return;
      end if;

      T1 := TimeFromLastClickToLastUpdate;
      T2 := TimeSinceLastUpdate;
      D1 := DistanceFromLastClickToLastUpdate;
      D2 := DistanceSinceLastUpdate;

      EstimatedGroundVelocityIsAvailable := True;
      EstimatedGroundVelocity := ((D1 + D2) * 3600) / (T1 + T2);
   end UpdateNGVelocity;
end NG_V2;
