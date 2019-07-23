------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2016-2019, Altran UK Limited                --
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

   procedure External_Timing (Timer : in out Time_Token;
                              Msg   : String;
                              Time  : Duration) is
   begin
      Timer.History.Append ((Name   => To_Unbounded_String (Msg),
                             Length => Time));
   end External_Timing;

   ------------------
   -- Timing_Start --
   ------------------

   procedure Timing_Start (Timer : out Time_Token)
   is
   begin
      Timer := (History => Histories.Empty_List,
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

      package Duration_IO is new Ada.Text_IO.Fixed_IO (Duration);

   begin
      if Debug_Mode then
         Put (Msg);
         for I in Msg'Length + 1 .. 35 loop
            Put (' ');
         end loop;
         --  Print elapsed time in 1234.5 notation; this is enough for around
         --  2.5 hours and if we hit this limit then we have other problems to
         --  worry about.
         Duration_IO.Put (Elapsed, Fore => 4, Aft => 1);
         Put_Line ("s");
      end if;
      Timer.History.Append ((Name   => To_Unbounded_String (Msg),
                             Length => Elapsed));
      Timer.Start := Now;
   end Timing_Phase_Completed;

   --------------------
   -- Timing_History --
   --------------------

   function Timing_History (Timer : Time_Token) return JSON_Value
   is
   begin
      return V : constant JSON_Value := Create_Object do
         for P of Timer.History loop
            Set_Field (V, To_String (P.Name), Float (P.Length));
         end loop;
      end return;
   end Timing_History;

end Debug.Timing;
