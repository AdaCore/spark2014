------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--            Copyright (C) 2016-2017, Altran UK Limited                    --
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

--  Package to help print where we spend time.

with GNATCOLL.JSON; use GNATCOLL.JSON;

private with Ada.Execution_Time;
private with Ada.Containers.Vectors;
private with Ada.Strings.Unbounded;

package Debug.Timing is

   type Time_Token is limited private;

   procedure Timing_Start (T : out Time_Token);
   --  The beginning of time. Or at least in our way of counting ;)

   procedure Timing_Phase_Completed (T : in out Time_Token;
                                     S : String);
   --  Note how much time has elapsed since the last call of this procedure
   --  (or the call to Timing_Start if it is called for the first time).
   --  Make sure S is unique if you want to call Timing_History.

   function Timing_History (T : Time_Token) return JSON_Value;
   --  Return the history so far as a mapping {string -> float} with
   --  elapsed phases (the string) and how long they took (the float).

   procedure External_Timing (T : in out Time_Token;
                              S : String;
                              Time : Float);
   --  inject a timing that comes from another source than this package. This
   --  allows to integrate timings from spawned processes into the output

private

   use Ada.Execution_Time;
   use Ada.Strings.Unbounded;

   type Deci_Seconds is new Integer;

   type Phase is record
      Name   : Unbounded_String;
      Length : Deci_Seconds;
   end record;

   package Histories is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Phase);
   use Histories;

   type Time_Token is record
      Time_Stamp : CPU_Time;
      History    : Vector;
   end record;

end Debug.Timing;
