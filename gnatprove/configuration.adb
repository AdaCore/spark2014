------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line;
with Ada.Text_IO;       use Ada.Text_IO;

with Hilitevsn; use Hilitevsn;

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Strings;      use GNAT.Strings;
with GNAT.OS_Lib;

with Call;              use Call;

package body Configuration is

   MMode_Input  : aliased GNAT.Strings.String_Access;
   --  The mode of gnatprove, and the input variable for command line parsing
   --  set by option --mode=
   Report_Input   : aliased GNAT.Strings.String_Access;
   --  The input variable for command line parsing set by option --report=

   procedure Do_Nothing (Switch    : String;
                         Parameter : String;
                         Section   : String);
   --  Dummy procedure.

   procedure Handle_Switch
     (Switch    : String;
      Parameter : String;
      Section   : String);
   --  Deal with all switches that are not automatic. In gnatprove, all
   --  recognized switches are automatic, so this procedure should only be
   --  called for unknown switches and for switches in section -cargs

   function Init return Project_Tree;
   --  Load the project file; This function requires the project file to be
   --  present.

   Usage_Message : constant String :=
      "switches [files] [-cargs switches]";

   Help_Message : constant String :=
"files is one or more file names, must be used with option -u" &
ASCII.LF &
"-cargs switches are passed to gcc" &
ASCII.LF &
ASCII.LF &
"gnatprove basic switches:" & ASCII.LF &
" -f                Force recompilation/proving of all units and all VCs" &
ASCII.LF &
" -jnnn             Use nnn parallel processes (default: 1)" &
ASCII.LF &
"     --mode=m      Set the mode of GNATprove (m=detect*,force,check,prove)" &
ASCII.LF &
" -Pproj            Use GNAT project file proj" &
ASCII.LF &
" -q, --quiet       Be quiet/terse" &
ASCII.LF &
"     --report=r    Set the report mode of GNATprove (r=fail*, all, detailed)"&
ASCII.LF &
" -u                Unique compilation, only prove the given files" &
ASCII.LF &
" -U                Prove all files of all projects" &

ASCII.LF &
" -v, --verbose     Output extra verbose information" &
ASCII.LF &
"     --version     Output version of the tool" &
ASCII.LF &
" -h, --help        Display this usage information" &
ASCII.LF &
ASCII.LF &
"gnatprove advanced switches:" &
ASCII.LF &
" -d, --debug       Debug mode" &
ASCII.LF &
"     --no-proof    Disable proof of VCs, only generate VCs" &
ASCII.LF &
"     --pedantic    Use a strict interpretation of the Ada standard" &
ASCII.LF &
"     --steps=nnn   Set the maximum number of proof steps to nnn for Alt-Ergo"&
ASCII.LF &
"     --timeout=s   Set the timeout for Alt-Ergo in seconds (default: 10)";

   ----------------
   -- Do_Nothing --
   ----------------

   procedure Do_Nothing (Switch    : String;
                         Parameter : String;
                         Section   : String) is
   begin
      null;
   end Do_Nothing;

   -------------------
   -- Handle_Switch --
   -------------------

   procedure Handle_Switch
     (Switch    : String;
      Parameter : String;
      Section   : String)
   is
   begin
      if Section = "cargs" then
         Cargs_List.Append (Switch & Separator & Parameter);
      elsif Switch (Switch'First) /= '-' then

         --  We assume that the "switch" is actually an argument and put it in
         --  the file list

         File_List.Append (Switch);
      else
         raise Invalid_Switch;

      end if;

   end Handle_Switch;

   ----------
   -- Init --
   ----------

   function Init return Project_Tree
   is
      Proj_Env  : Project_Environment_Access;
      GNAT_Version : GNAT.Strings.String_Access;
      Tree      : Project_Tree;

   begin
      Initialize (Proj_Env);
      Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
      Set_Object_Subdir (Proj_Env.all, Subdir_Name);
      Proj_Env.Register_Default_Language_Extension ("C", ".h", ".c");
      declare
         S : constant String :=
           Register_New_Attribute ("Switches", "Prove", Is_List => True);
      begin
         if S /= "" then
            Abort_With_Message (S);
         end if;
      end;
      if Project_File.all /= "" then
         Tree.Load
           (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
            Proj_Env);
      else
         Abort_With_Message ("No project file is given, aborting");
      end if;

      return Tree;
   end Init;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project_Tree)
   is
      Config : Command_Line_Configuration;

      procedure Abort_With_Help (Msg : String);
      --  Stop the program, output the message and the help message, then exit

      ---------------------
      -- Abort_With_Help --
      ---------------------

      procedure Abort_With_Help (Msg : String)
      is
      begin
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
         Ada.Text_IO.New_Line;
         Display_Help (Config);
         GNAT.OS_Lib.OS_Exit (1);
      end Abort_With_Help;

      First_Config : Command_Line_Configuration;
      Com_Lin : aliased String_List :=
        (1 .. Ada.Command_Line.Argument_Count => <>);
   begin

      --  First, copy the command line

      for Index in 1 .. Com_Lin'Last loop
         Com_Lin (Index) :=
           new String'(Ada.Command_Line.Argument (Index));
      end loop;

      --  Let's do a first parse to get the project file, if any:

      Set_Usage
        (First_Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      Define_Switch
        (First_Config, Project_File'Access,
         "-P:",
         Help => "The name of the project file");

      Define_Switch (First_Config, "*", Help => "list of source files");

      Getopt (First_Config,
              Callback => Do_Nothing'Access,
              Concatenate => False);

      --  Install command line config

      Set_Usage
        (Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      Define_Switch
         (Config,
          Debug'Access,
          "-d", Long_Switch => "--debug",
          Help => "Debug mode");

      Define_Switch
        (Config, Project_File'Access,
         "-P:",
         Help => "The name of the project file");

      Define_Switch
        (Config,
         Force'Access,
         "-f",
         Help => "Force recompilation / proving of all units and all VCs");

      Define_Switch
         (Config, Parallel'Access,
          Long_Switch => "-j:",
          Help => "Set the number of parallel processes (default is 1)");

      Define_Switch
        (Config,
         MMode_Input'Access,
         Long_Switch => "--mode=",
         Help => "Set the mode of GNATprove (detect | force | check)");

      Define_Switch
        (Config,
         No_Proof'Access,
         Long_Switch => "--no-proof",
         Help => "Disable proof of VCs, only generate VCs");

      Define_Switch
        (Config,
         Pedantic'Access,
         Long_Switch => "--pedantic",
         Help => "Use a strict interpretation of the Ada standard");

      Define_Switch
         (Config,
          Quiet'Access,
          "-q", Long_Switch => "--quiet",
          Help => "Be quiet/terse");

      Define_Switch
        (Config,
         Report_Input'Access,
         Long_Switch => "--report=",
         Help => "Set the report mode of GNATprove (fail| all| detailed)");

      Define_Switch
         (Config, Steps'Access,
          Long_Switch => "--steps=",
          Help => "Set the maximum number of proof steps for Alt-Ergo");

      Define_Switch
         (Config, Timeout'Access,
          Long_Switch => "--timeout=",
          Help => "Set the timeout for Alt-Ergo in seconds (default is 10)");

      Define_Switch
         (Config,
          Only_Given'Access,
          "-u",
          Help => "Unique compilation - only compile/prove the given files");

      Define_Switch
         (Config,
          All_Projects'Access,
          "-U",
          Help => "Unique compilation for all sources of all projects");

      Define_Switch
        (Config,
         Verbose'Access,
         "-v", Long_Switch => "--verbose",
         Help => "Output extra verbose information");

      Define_Switch
        (Config,
         Version'Access,
         Long_Switch => "--version",
         Help => "Output version of the tool");

      Define_Switch
        (Config,
         Limit_Line'Access,
         Long_Switch => "--limit-line=",
         Help => "Limit proofs to given file and line");

      Define_Switch (Config, "*", Help => "list of source files");

      Define_Section (Config, "cargs");
      Define_Switch (Config, "*", Section => "cargs");

      Tree := Init;
      declare
         Proj_Type      : constant Project_Type := Root_Project (Tree);
         Extra_Switches : constant String_List_Access :=
           Attribute_Value (Proj_Type, Build ("Prove", "Switches"));
      begin
         if Extra_Switches /= null then
            declare
               All_Switches   : aliased constant String_List :=
                 Extra_Switches.all & Com_Lin;
               All_Access     : constant String_List_Access :=
                 new String_List'(All_Switches);
               Parser         : Opt_Parser;
            begin
               Initialize_Option_Scan (Parser, All_Access);
               Getopt (Config,
                       Callback => Handle_Switch'Access,
                       Parser   => Parser,
                       Concatenate => False);
            end;
         else
            Getopt (Config,
                    Callback => Handle_Switch'Access,
                    Concatenate => False);
         end if;
      end;

      if Version then
         Ada.Text_IO.Put_Line (Hilite_Version_String);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      if MMode_Input.all = "detect" or else MMode_Input.all = "" then
         MMode := GPM_Detect;
      elsif MMode_Input.all = "force" then
         MMode := GPM_Force;
      elsif MMode_Input.all = "check" then
         MMode := GPM_Check;
      elsif MMode_Input.all = "prove" then
         MMode := GPM_Prove;
      else
         Abort_With_Help ("mode should be one of (detect | force | check)");
      end if;

      if Report_Input.all = "fail" or else Report_Input.all = "" then
         Report := GPR_Fail;
      elsif Report_Input.all = "all" then
         Report := GPR_Verbose;
      elsif Report_Input.all = "detailed" then
         Report := GPR_Detailed;
      else
         Abort_With_Help
           ("report should be one of (fail | all | detailed)");
      end if;

      if Limit_Line /= null and then Limit_Line.all /= "" then

         --  Limit_Line implies -u for the file. We realize this here, but we
         --  take care to only add a body to the list for -u

         declare
            Index : Integer := Limit_Line.all'Last;
         begin
            while Index > Limit_Line.all'First and then
              Limit_Line.all (Index) /= ':' loop
               Index := Index - 1;
            end loop;
            if Index = Limit_Line.all'First then
               Abort_With_Message
                 ("limit-line: incorrect line specification - missing ':'");
            end if;
            declare
               Limit_File : constant String :=
                 Limit_Line.all (Limit_Line.all'First .. Index - 1);
               Limit_VF : constant Virtual_File :=
                 Create_From_Base (Filesystem_String (Limit_File));
               Restrict : Virtual_File;
            begin
               if Unit_Part (Tree.Info (Limit_VF)) = Unit_Body then
                  Restrict := Limit_VF;
               else
                  Restrict := Tree.Other_File (Limit_VF);
               end if;
               File_List.Append (String (Base_Name (Restrict)));
            end;
         end;
         Only_Given := True;
      end if;
   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
      when Invalid_Parameter =>
         Abort_With_Help ("No parameter given to switch -" & Full_Switch);
   end Read_Command_Line;

end Configuration;
