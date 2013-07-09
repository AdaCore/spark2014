------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y - A R G S                       --
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

with Ada.Environment_Variables;
with Ada.Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Output;                use Output;
with Types;                 use Types;

package body Gnat2Why_Args is

   Env_Variable_Name : constant String := "GNAT2WHY_ARGS";

   Standard_Mode_Name      : constant String := "standard_mode";
   Check_Mode_Name         : constant String := "check_mode";
   Flow_Analysis_Mode_Name : constant String := "flow_analysis_mode";
   Flow_Dump_Graphs_Name   : constant String := "flow_dump_graphs";
   Analyze_File_Name       : constant String := "analyze_file";

   procedure Interpret_Token (Token : String);
   --  This procedure should be called on an individual token in the
   --  environment variable. It will set the corresponding boolean variable to
   --  True. The program is stopped if an unrecognized option is encountered.

   ----------
   -- Init --
   ----------

   procedure Init is
      Args_String : constant String :=
        Ada.Environment_Variables.Value (Env_Variable_Name, Default => "");
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
      if Token = Standard_Mode_Name then
         Standard_Mode := True;
      elsif Token = Check_Mode_Name then
         Check_Mode := True;
      elsif Token = Flow_Analysis_Mode_Name then
         Flow_Analysis_Mode := True;
      elsif Token = Flow_Dump_Graphs_Name then
         Flow_Dump_Graphs := True;
      elsif Starts_With (Token, Analyze_File_Name) and then
        Token (Token'First + Analyze_File_Name'Length) = '='
      then
         declare
            Start : constant Integer :=
              Token'First + Analyze_File_Name'Length + 1;
         begin
            Analyze_File.Append (Token (Start .. Token'Last));
         end;
      else

         --  We play it safe and quit if there is an unrecognized option

         Write_Str ("error: unrecognized option" & Token & " given");
         Write_Eol;
         raise Terminate_Program;
      end if;
   end Interpret_Token;

   ---------
   -- Set --
   ---------

   procedure Set (Debug : Boolean) is
      Val : Unbounded_String := Null_Unbounded_String;
   begin
      if Standard_Mode then
         Append (Val, ' ');
         Append (Val, Standard_Mode_Name);
      end if;
      if Check_Mode then
         Append (Val, ' ');
         Append (Val, Check_Mode_Name);
      end if;
      if Flow_Analysis_Mode then
         Append (Val, ' ');
         Append (Val, Flow_Analysis_Mode_Name);
      end if;
      if Flow_Dump_Graphs then
         Append (Val, ' ');
         Append (Val, Flow_Dump_Graphs_Name);
      end if;
      for File of Analyze_File loop
         Append (Val, ' ');
         Append (Val, Analyze_File_Name);
         Append (Val, '=');
         Append (Val, File);
      end loop;
      if Val /= "" then
         declare
            Val_Str : constant String := To_String (Val);
         begin
            if Debug then
               Ada.Text_IO.Put_Line ("Setting " & Env_Variable_Name &
                                     " to """ & Val_Str & """");
            end if;
            Ada.Environment_Variables.Set (Name  => Env_Variable_Name,
                                           Value => Val_Str);
         end;
      end if;
   end Set;

   -----------
   -- Clear --
   -----------

   procedure Clear is
   begin
      Ada.Environment_Variables.Clear (Env_Variable_Name);
   end Clear;

end Gnat2Why_Args;
