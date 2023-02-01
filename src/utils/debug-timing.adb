------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2016-2023, Capgemini Engineering              --
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

with Ada.Text_IO;   use Ada.Text_IO;
with Gnat2Why_Args; use Gnat2Why_Args;

package body Debug.Timing is

   ---------------------
   -- External_Timing --
   ---------------------

   procedure Register_Timing (Timer  : in out Time_Token;
                              Entity : Subp_Type;
                              Msg    : String;
                              Time   : Duration) is
      use Timings;
      package Duration_IO is new Ada.Text_IO.Fixed_IO (Duration);

      procedure Insert_Entity (Key : Subp_Type; Element : in out Timings.Map);
      --  Callback add the timing to the element mapped to the Subp Key

      procedure Insert_Timing (Key : String; Element : in out Duration);
      --  Callback to add the duration to the value already mapped to the event
      --  Key.

      -------------------
      -- Insert_Timing --
      -------------------

      procedure Insert_Timing (Key : String; Element : in out Duration) is
         pragma Unreferenced (Key);
      begin
         Element := Element + Time;
         if Debug_Mode then
            Put (Msg);
            for I in Msg'Length + 1 .. 60 loop
               Put (' ');
            end loop;
            --  Print elapsed time in 1234.5 notation; this is enough for
            --  around 2.5 hours and if we hit this limit then we have other
            --  problems to worry about.
            Duration_IO.Put (Element, Fore => 4, Aft => 1);
            Put_Line ("s");
         end if;
      end Insert_Timing;

      -------------------
      -- Insert_Entity --
      -------------------

      procedure Insert_Entity (Key : Subp_Type; Element : in out Timings.Map)
      is
         pragma Unreferenced (Key);
         C : Timings.Cursor;
         Unused : Boolean;
      begin
         Element.Insert (Msg, 0.0, C, Unused);
         Element.Update_Element (C, Insert_Timing'Access);
      end Insert_Entity;

      C      : Entity_Maps.Cursor := Timer.History.Find (Entity);
      Unused : Boolean;
   begin
      Timer.History.Insert (Entity, Timings.Empty_Map, C, Unused);
      Timer.History.Update_Element (C, Insert_Entity'Access);
   end Register_Timing;

   ------------------
   -- Timing_Start --
   ------------------

   procedure Timing_Start (Timer : out Time_Token)
   is
   begin
      Timer := (History => Entity_Maps.Empty_Map,
                Start   => Ada.Calendar.Clock);
   end Timing_Start;

   ----------------------------
   -- Timing_Phase_Completed --
   ----------------------------

   procedure Timing_Phase_Completed (Timer  : in out Time_Token;
                                     Entity : Subp_Type;
                                     Msg    : String)
   is

      use Ada.Calendar;

      Now     : constant Time := Clock;
      Elapsed : constant Duration := Now - Timer.Start;

   begin
      Register_Timing (Timer, Entity, Msg, Elapsed);
      Timer.Start := Now;
   end Timing_Phase_Completed;

   --------------------
   -- Timing_History --
   --------------------

   function Timing_History (Timer : Time_Token) return JSON_Value
   is
      Result : constant JSON_Value := Create_Object;
   begin
      for P in Timer.History.Iterate loop
         declare
            Obj      : constant JSON_Value := Create_Object;
            Key      : constant Subp_Type := Entity_Maps.Key (P);
            JSON_Key : constant String :=
              (if Is_Null (Key) then "global" else To_Key (Key));
         begin
            for Q in Entity_Maps.Element (P).Iterate loop
               Set_Field (Obj, Timings.Key (Q), Float (Timings.Element (Q)));
            end loop;
            Set_Field (Result, JSON_Key, Obj);
         end;
      end loop;
      return Result;
   end Timing_History;

end Debug.Timing;
