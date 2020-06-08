with Interfaces; use Interfaces;

package Failsafe with SPARK_Mode,
  Abstract_State => Failsafe_State,
  Initializes => (Failsafe_State, Model.Battery_Level_At, Model.Current_Time)
is
   pragma Unevaluated_Use_Of_Old(Allow);

   type Battery_Level_Type is new Float;
   Battery_Threshold : constant Battery_Level_Type := 0.20;
   Failsafe_Cycles : constant := 50;

   package Model with Ghost is

      type Time_Slot is mod Failsafe_Cycles;
      subtype Time_Slot_Length is Unsigned_8 range 0 .. Failsafe_Cycles;
      type Battery_Level_Over_Time is array (Time_Slot) of Battery_Level_Type;

      Battery_Level_At : Battery_Level_Over_Time := (others => 1.0);
      Current_Time : Time_Slot := Time_Slot'First;

      function Time_Below_Threshold return Time_Slot_Length with
        Contract_Cases =>
          --  Current battery level is above threshold
          (Battery_Level_At(Current_Time) >= Battery_Threshold =>
             Time_Below_Threshold'Result = 0,

           --  Battery level in all past cycles was below threshold
           (for all S in Time_Slot => Battery_Level_At(S) < Battery_Threshold) =>
             Time_Below_Threshold'Result = Time_Slot_Length'Last,

           --  otherwise, battery level was above threshold in some time in the
           --  past, and is now below threshold
           others =>
             Time_Below_Threshold'Result < Time_Slot_Length'Last
               and then
             Battery_Level_At(Current_Time - Time_Slot(Time_Below_Threshold'Result)) >= Battery_Threshold
               and then
             (if Current_Time >= Time_Slot (Time_Below_Threshold'Result - 1) then
                (for all S in Current_Time - (Time_Slot(Time_Below_Threshold'Result - 1)) .. Current_Time
                 => Battery_Level_At(S) < Battery_Threshold)
              else
                (for all S in 0 .. Current_Time => Battery_Level_At(S) < Battery_Threshold)
                   and then
                (for all S in Current_Time - (Time_Slot(Time_Below_Threshold'Result - 1)) .. Time_Slot'Last
                 => Battery_Level_At(S) < Battery_Threshold)));

      function Is_Valid return Boolean;

   end Model;

   use Model;

   procedure Update (Battery_Level : in Battery_Level_Type) with
     Pre => Is_Valid,
     Post => Is_Valid
       and then Current_Time = Current_Time'Old + 1
       and then Battery_Level_At(Current_Time) = Battery_Level;

   function Is_Raised return Boolean with
     Pre  => Is_Valid,
     Post => Is_Valid
       and then Is_Raised'Result = (Time_Below_Threshold >= Failsafe_Cycles);

end Failsafe;
