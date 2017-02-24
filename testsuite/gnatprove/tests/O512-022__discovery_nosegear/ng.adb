package body NG is

   --  Interface to sensors

   function Millisecs return Mod_Time is
   begin
      --  any value for testing
      return 100;
   end Millisecs;

   function NGClickTime return Mod_Time is
   begin
      --  any value for testing
      return 5;
   end NGClickTime;

   function NGRotations return Mod_Count is
   begin
      --  any value for testing
      return 20;
   end NGRotations;

   --  API

   procedure ComputeNGVelocity
     (CurrTime  : in     Mod_Time;
      ThisTime  : in     Mod_Time;
      ThisCount : in     Mod_Count;
      Success   :    out Boolean;
      Result    :    out Velocity)
   with
     Pre => ThisTime /= PrevTime and then ThisCount /= PrevCount,
     Post => (if Success then
                Result =
                  Velocity(
                  (((WHCF * Integer (ThisCount - PrevCount)) +
                     ((WHCF * Integer (ThisCount - PrevCount))
                     * Integer (CurrTime - ThisTime))
                     / Integer (ThisTime - PrevTime))
                  * 3600)
                  / Integer (CurrTime - PrevTime)));

   procedure ComputeNGVelocity
     (CurrTime  : in     Mod_Time;
      ThisTime  : in     Mod_Time;
      ThisCount : in     Mod_Count;
      Success   :    out Boolean;
      Result    :    out Velocity)
   is
      T1, T2 : Time;
      D1, D2 : Distance;
   begin
      if ThisCount - PrevCount < ThisTime - PrevTime then
         Success := False;
         Result  := 0;
         return;
      end if;

      T1 := Time (ThisTime - PrevTime);
      T2 := Time (CurrTime - ThisTime);
      D1 := WHCF * Count (ThisCount - PrevCount);
      D2 := (D1 * T2) / T1;

      Success := True;
      Result  := ((D1 + D2) * 3600) / (T1 + T2);
   end ComputeNGVelocity;

   procedure UpdateNGVelocity is
      CurrTime  : Mod_Time := Millisecs;
      ThisTime  : Mod_Time := NGClickTime;
      ThisCount : Mod_Count := NGRotations;
   begin
      if ThisTime = PrevTime then
         EstimatedGroundVelocityIsAvailable := False;
         return;
      end if;

      ComputeNGVelocity (CurrTime, ThisTime, ThisCount,
                         EstimatedGroundVelocityIsAvailable,
                         EstimatedGroundVelocity);
   end UpdateNGVelocity;
end NG;
