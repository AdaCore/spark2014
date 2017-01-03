------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          D E B U G . T I M I N G                         --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Real_Time;       use Ada.Real_Time;

with Gnat2Why_Args;       use Gnat2Why_Args;

package body Debug.Timing is

   function To_Deci_Seconds (T : Time_Span) return Deci_Seconds;
   --  Convert the T to deci-seconds, truncating (instead of rounding).

   function To_Unbounded_String (DS : Deci_Seconds) return Unbounded_String;
   --  Convert deci-seconds to a string (e.g. "12.3")

   function To_Float (DS : Deci_Seconds) return Float;
   --  Convert deci-seconds to a float.

   ---------------------
   -- External_Timing --
   ---------------------

   procedure External_Timing (T : in out Time_Token;
                              S : String;
                              Time : Float) is
   begin
      T.History.Append ((Name   => To_Unbounded_String (S),
                         Length => Deci_Seconds (Time * 10.0)));
   end External_Timing;

   ---------------------
   -- To_Deci_Seconds --
   ---------------------

   function To_Deci_Seconds (T : Time_Span) return Deci_Seconds
   is (Deci_Seconds (T / Milliseconds (100)));

   -------------------------
   -- To_Unbounded_String --
   -------------------------

   function To_Unbounded_String (DS : Deci_Seconds) return Unbounded_String
   is
      Seconds  : Integer          := Integer (DS) / 10;
      Fraction : constant Integer := Integer (DS) mod 10;
   begin
      return S : Unbounded_String := Null_Unbounded_String do
         while Seconds > 0 or Length (S) = 0 loop
            S := S & Character'Val (Character'Pos ('0') + Seconds mod 10);
            Seconds := Seconds / 10;
         end loop;
         Append (S, ".");
         Append (S, Character'Val (Character'Pos ('0') + Fraction));
      end return;
   end To_Unbounded_String;

   --------------
   -- To_Float --
   --------------

   function To_Float (DS : Deci_Seconds) return Float
   is (Float (DS) / 10.0);

   ------------------
   -- Timing_Start --
   ------------------

   procedure Timing_Start (T : out Time_Token)
   is
   begin
      T := (Time_Stamp => Clock,
            History    => Empty_Vector);
   end Timing_Start;

   ----------------------------
   -- Timing_Phase_Completed --
   ----------------------------

   procedure Timing_Phase_Completed (T : in out Time_Token;
                                     S : String)
   is
      Now     : constant CPU_Time     := Clock;
      Elapsed : constant Deci_Seconds := To_Deci_Seconds (Now - T.Time_Stamp);
   begin
      if Debug_Mode then
         Put (S);
         for I in S'Length + 1 .. 35 loop
            Put (' ');
         end loop;
         Put (" (");
         Put (To_String (To_Unbounded_String (Elapsed)));
         Put_Line ("s)");
      end if;
      T.History.Append ((Name   => To_Unbounded_String (S),
                         Length => Elapsed));
      T.Time_Stamp := Now;
   end Timing_Phase_Completed;

   --------------------
   -- Timing_History --
   --------------------

   function Timing_History (T : Time_Token) return JSON_Value
   is
   begin
      return V : constant JSON_Value := Create_Object do
         for P of T.History loop
            Set_Field (V, To_String (P.Name), To_Float (P.Length));
         end loop;
      end return;
   end Timing_History;

end Debug.Timing;
