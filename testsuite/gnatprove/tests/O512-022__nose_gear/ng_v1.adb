package body NG_V1 is

   --  Interface to sensors

   function Millisecs return Unsigned_16;
   pragma Import (C, Millisecs);

   function NGClickTime return Unsigned_16;
   pragma Import (C, NGClickTime);

   function NGRotations return Unsigned_16;
   pragma Import (C, NGRotations);

   --  API

   function DistanceFromLastClickToLastUpdate return Unsigned_16 is
      (WHCF * (ThisCount - PrevCount));

   procedure UpdateNGVelocity is
      T1, T2, D1, D2 : Unsigned_16;
   begin
      if ThisTime = PrevTime then
         EstimatedGroundVelocityIsAvailable := False;
         return;
      end if;

      T1 := ThisTime - PrevTime;
      T2 := CurrTime - ThisTime;
      D1 := WHCF * (ThisCount - PrevCount);
      D2 := (D1 * T2) / T1;

      EstimatedGroundVelocityIsAvailable := True;
      EstimatedGroundVelocity := ((D1 + D2) * 3600) / (T1 + T2);
   end UpdateNGVelocity;
end NG_V1;
