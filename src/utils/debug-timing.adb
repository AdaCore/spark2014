------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2016-2021, Altran UK Limited                --
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

with Ada.Text_IO;          use Ada.Text_IO;
with Gnat2Why_Args;        use Gnat2Why_Args;

package body Debug.Timing is

   ---------------------
   -- External_Timing --
   ---------------------

   procedure Register_Timing (Timer : in out Time_Token;
                              Msg   : String;
                              Time  : Duration) is
      use Timings;
      package Duration_IO is new Ada.Text_IO.Fixed_IO (Duration);

      C         : Cursor;
      Inserted  : Boolean;
      New_Total : Duration;
   begin
      Timer.History.Insert
        (Key      => Msg,
         New_Item => Time,
         Position => C,
         Inserted => Inserted);

      if not Inserted then
         New_Total := Element (C) + Time;
         Timer.History.Replace_Element (C, New_Total);
      else
         New_Total := Time;
      end if;
      if Debug_Mode then
         Put (Msg);
         for I in Msg'Length + 1 .. 60 loop
            Put (' ');
         end loop;
         --  Print elapsed time in 1234.5 notation; this is enough for around
         --  2.5 hours and if we hit this limit then we have other problems to
         --  worry about.
         Duration_IO.Put (New_Total, Fore => 4, Aft => 1);
         Put_Line ("s");
      end if;
   end Register_Timing;

   ------------------
   -- Timing_Start --
   ------------------

   procedure Timing_Start (Timer : out Time_Token)
   is
   begin
      Timer := (History => Timings.Empty_Map,
                Start   => Ada.Calendar.Clock);
   end Timing_Start;

   ----------------------------
   -- Timing_Phase_Completed --
   ----------------------------

   procedure Timing_Phase_Completed (Timer : in out Time_Token;
                                     Msg   : String)
   is
      use Ada.Calendar;

      Now     : constant Time := Clock;
      Elapsed : constant Duration := Now - Timer.Start;

   begin
      Register_Timing (Timer, Msg, Elapsed);
      Timer.Start := Now;
   end Timing_Phase_Completed;

   --------------------
   -- Timing_History --
   --------------------

   function Timing_History (Timer : Time_Token) return JSON_Value
   is
      use Timings;
   begin
      return V : constant JSON_Value := Create_Object do
         for P in Timer.History.Iterate loop
            Set_Field (V, Key (P), Float (Element (P)));
         end loop;
      end return;
   end Timing_History;

end Debug.Timing;
