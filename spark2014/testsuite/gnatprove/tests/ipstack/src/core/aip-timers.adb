------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

package body AIP.Timers with
  SPARK_Mode => Off
is

   use type Time_Types.Time;

   type Timer is record
      Interval   : Time_Types.Interval := 0;
      Last_Event : Time_Types.Time     := Time_Types.Time'First;
   end record;

   type Timer_Array is array (Timer_Id) of Timer;
   My_Timers : Timer_Array;

   function Deadline (T : Timer) return Time_Types.Time;
   --  Return the next deadline for the given timer

   --------------
   -- Deadline --
   --------------

   function Deadline (T : Timer) return Time_Types.Time is
   begin
      if T.Interval = 0 then
         return Time_Types.Time'Last;
      else
         return T.Last_Event + T.Interval;
      end if;
   end Deadline;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      null;
   end Initialize;

   -------------------
   -- Next_Deadline --
   -------------------

   function Next_Deadline return Time_Types.Time is
      Result : Time_Types.Time := Time_Types.Time'Last;
      My_Deadline : Time_Types.Time;
   begin
      for J in My_Timers'Range loop
         My_Deadline := Deadline (My_Timers (J));
         if My_Deadline < Result then
            Result := My_Deadline;
         end if;
      end loop;
      return Result;
   end Next_Deadline;

   ------------------
   -- Set_Interval --
   ------------------

   procedure Set_Interval
     (TID      : Timer_Id;
      Interval : Time_Types.Interval)
   is
   begin
      My_Timers (TID).Interval := Interval;
   end Set_Interval;

   -----------------
   -- Timer_Fired --
   -----------------

   function Timer_Fired
     (Now : Time_Types.Time;
      TID : Timer_Id) return Boolean
   is
      My_Timer : Timer renames My_Timers (TID);
   begin
      if My_Timer.Interval > 0
        and then My_Timer.Last_Event + My_Timer.Interval <= Now
      then
         My_Timer.Last_Event := Now;
         return True;
      else
         return False;
      end if;

   end Timer_Fired;

end AIP.Timers;
