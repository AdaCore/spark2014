------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2019, Altran UK Limited                --
--                     Copyright (C) 2016-2019, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

--  Package to help print where we spend time

with GNATCOLL.JSON; use GNATCOLL.JSON;

private with Ada.Calendar;
private with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Hash;

package Debug.Timing is

   type Time_Token is limited private;

   procedure Timing_Start (Timer : out Time_Token);
   --  The beginning of time. Or at least in our way of counting ;)

   procedure Timing_Phase_Completed (Timer : in out Time_Token;
                                     Msg   : String);
   --  Note how much time has elapsed since the last call of this procedure
   --  (or the call to Timing_Start if it is called for the first time).
   --  Make sure Msg is unique if you want to call Timing_History.

   function Timing_History (Timer : Time_Token) return JSON_Value;
   --  Return the history so far as a mapping {string -> float} with
   --  elapsed phases (the string) and how long they took (the float).

   procedure Register_Timing (Timer : in out Time_Token;
                              Msg   : String;
                              Time  : Duration)
   with Pre => Time >= 0.0;
   --  Inject a timing that comes from another source than this package. This
   --  allows to integrate timings from spawned processes into the output.
   --  Unlike timing coming from this package, the external times should be
   --  non-negative.

private

   --  Timing relies on Ada.Calendar and not Ada.Execution_Time, because the
   --  latter would force the use of Ada.Real_Time and in turn the GNAT tasking
   --  runtime, which incurs performance penalty at each allocation and
   --  deallocation (and we have plenty of those). Here we only care about
   --  estimate timing, so the less-precise and potentially non-monotonic clock
   --  from Ada.Calendar is acceptable.

   package Timings is new Ada.Containers.Indefinite_Hashed_Maps
     (Key_Type        => String,
      Element_Type    => Duration,
      Hash            => Ada.Strings.Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   type Time_Token is record
      Start   : Ada.Calendar.Time;
      History : Timings.Map;
   end record;

end Debug.Timing;
