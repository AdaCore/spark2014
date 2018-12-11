--
-- Copyright (C) 2015-2016 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

private package HW.Time.Timer
   with
      Abstract_State => ((Timer_State with Part_Of => HW.Time.State),
                         (Abstract_Time with
                           Part_Of => HW.Time.State,
                           External => Async_Writers)),
      Initializes => (Timer_State)
is

   -- Returns the highest point in time that has definitely passed.
   function Raw_Value_Min return T
   with
      Volatile_Function,
      Global => (Input => Abstract_Time),
      Depends => (Raw_Value_Min'Result => Abstract_Time);

   -- Returns the highest point in time that might have been reached yet.
   function Raw_Value_Max return T
   with
      Volatile_Function,
      Global => (Input => Abstract_Time),
      Depends => (Raw_Value_Max'Result => Abstract_Time);

   function Hz return T
   with
      Global => (Input => Timer_State);

end HW.Time.Timer;
