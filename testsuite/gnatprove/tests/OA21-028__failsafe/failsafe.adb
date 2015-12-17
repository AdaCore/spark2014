package body Failsafe with SPARK_Mode,
  Refined_State => (Failsafe_State => Counter)
is
   Counter : Unsigned_8 range 0 .. Failsafe_Cycles := 0;

   package body Model is
      function Time_Below_Threshold return Time_Slot_Length is
         Res : Time_Slot_Length := 0;
      begin
         for S in Time_Slot loop
            if Battery_Level_At (Current_Time - S) < Battery_Threshold then
               Res := Res + 1;
            else
               exit;
            end if;
            pragma Assert (Res in 1 .. Failsafe_Cycles);
            pragma Loop_Invariant
              (if Current_Time >= Time_Slot (Res - 1) then
                 (for all S in Current_Time - Time_Slot(Res - 1) .. Current_Time
                  => Battery_Level_At(S) < Battery_Threshold)
               else
                 (for all S in 0 .. Current_Time => Battery_Level_At(S) < Battery_Threshold)
                    and then
                 (for all S in Current_Time - Time_Slot(Res - 1) .. Time_Slot'Last
                  => Battery_Level_At(S) < Battery_Threshold));
            pragma Loop_Invariant (Res = Time_Slot_Length(S) + 1);
         end loop;
         return Res;
      end Time_Below_Threshold;

      function Is_Valid return Boolean is
         (Counter = Time_Below_Threshold);
   end Model;

   procedure Update (Battery_Level : in Battery_Level_Type) is
      C : constant Unsigned_8 := Counter;
   begin
      pragma Assert (Counter = Time_Below_Threshold);
      pragma Assert (if (for all S in Time_Slot => Battery_Level_At(S) < Battery_Threshold)
                     then Counter = Time_Slot_Length'Last);
      pragma Assert (if (for all S in Time_Slot =>
                           (if S /= Current_Time + 1 then Battery_Level_At(S) < Battery_Threshold))
                     then Counter >= Time_Slot_Length'Last - 1);

      Current_Time := Current_Time + 1;
      Battery_Level_At(Current_Time) := Battery_Level;

      if Battery_Level < Battery_Threshold then
         Counter := Unsigned_8'Min(Counter + 1, Failsafe_Cycles);
         pragma Assert (if Battery_Level_At(Current_Time) >= Battery_Threshold
                        then Counter = 0);
         pragma Assert (if C = Time_Slot_Length'Last
                        then Counter = Time_Slot_Length'Last);
         pragma Assert (if C /= Time_Slot_Length'Last and
                          (for all S in Time_Slot => Battery_Level_At(S) < Battery_Threshold)
                        then
                           C = Time_Slot_Length'Last - 1);
         pragma Assert (if C /= Time_Slot_Length'Last and
                          (for all S in Time_Slot => Battery_Level_At(S) < Battery_Threshold)
                        then
                           Counter = Time_Slot_Length'Last);
         pragma Assert (if Battery_Level_At(Current_Time) < Battery_Threshold
                          and not (for all S in Time_Slot => Battery_Level_At(S) < Battery_Threshold)
                        then
                          Battery_Level_At(Current_Time - Time_Slot(Counter)) >= Battery_Threshold
                            and then
                          (if Current_Time >= Time_Slot (Counter - 1) then
                             (for all S in Current_Time - (Time_Slot(Counter - 1)) .. Current_Time
                              => Battery_Level_At(S) < Battery_Threshold)
                           else
                             (for all S in 0 .. Current_Time => Battery_Level_At(S) < Battery_Threshold)
                                and then
                             (for all S in Current_Time - (Time_Slot(Counter - 1)) .. Time_Slot'Last
                              => Battery_Level_At(S) < Battery_Threshold)));

         pragma Assert (Counter = Time_Below_Threshold);
      else
         Counter := 0;
      end if;
   end Update;

   function Is_Raised return Boolean is
     (Counter >= Failsafe_Cycles);

end Failsafe;
