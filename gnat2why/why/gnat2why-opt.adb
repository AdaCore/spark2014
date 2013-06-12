------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y - O P T                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Environment_Variables; use Ada.Environment_Variables;

with Output; use Output;
with Types;  use Types;

package body Gnat2Why.Opt is

   Env_Variable_Name : constant String := "GNAT2WHY_ARGS";

   procedure Interpret_Token (Token : String);
   --  This procedure should be called on an individual token in the
   --  environment variable. It will set the corresponding boolean variable to
   --  True. The program is stopped if an unrecognized option is encountered.

   ----------
   -- Init --
   ----------

   procedure Init is
      Args_String : constant String :=
        Value (Env_Variable_Name, Default => "");
      Start : Integer := Args_String'First;
   begin
      while Start in Args_String'Range loop
         declare
            Ending : Integer := Start;
         begin

            --  Search for the next blank and store its position in [Ending]

            while Ending in Args_String'Range and then
              Args_String (Ending) /= ' ' loop
               Ending := Ending + 1;
            end loop;

            if Start /= Ending then

               --  We have recognized a token, take it into account

               Interpret_Token (Args_String (Start .. Ending - 1));

            else

               --  Here we have Start = Ending, so either there are two spaces
               --  in a row, or a space at the start, or we are at the end of
               --  the string. In any case, we just continue.

               null;

            end if;

            Start := Ending + 1;
         end;
      end loop;
   end Init;

   ---------------------
   -- Interpret_Token --
   ---------------------

   procedure Interpret_Token (Token : String) is
   begin
      if Token = "standard_mode" then
         Standard_Mode := True;
      elsif Token = "check_mode" then
         Check_Mode := True;
      elsif Token = "flow_analysis_mode" then
         Flow_Analysis_Mode := True;
      elsif Token = "flow_dump_graphs" then
         Flow_Dump_Graphs := True;
      else

         --  We play it safe and quit if there is an unrecognized option

         Write_Str ("error: unrecognized option" & Token & " given");
         Write_Eol;
         raise Terminate_Program;
      end if;
   end Interpret_Token;

end Gnat2Why.Opt;
