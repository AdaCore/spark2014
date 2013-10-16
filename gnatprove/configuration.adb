------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
with Ada.Text_IO;               use Ada.Text_IO;
with System.Multiprocessors;

with SPARK2014VSN;              use SPARK2014VSN;

with GNAT.Command_Line;         use GNAT.Command_Line;
with GNAT.Directory_Operations;
with GNAT.Strings;              use GNAT.Strings;
with GNAT.OS_Lib;

with Call;                      use Call;

package body Configuration is

   MMode_Input  : aliased GNAT.Strings.String_Access;
   --  The mode of gnatprove, and the input variable for command line parsing
   --  set by option --mode=

   Warning_Input : aliased GNAT.Strings.String_Access;
   --  The warnings mode of gnatprove, and the input variable for command line
   --  parsing set by option --warnings=

   Report_Input : aliased GNAT.Strings.String_Access;
   --  The input variable for command line parsing set by option --report=

   Proof_Input  : aliased GNAT.Strings.String_Access;
   --  The input variable for command line parsing set by option --proof

   Clean        : aliased Boolean;
   --  Set to True when --clean was given. Triggers clean_up of GNATprove
   --  intermediate files.

   procedure Clean_Up (Tree : Project_Tree);

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

   procedure Sanitize_File_List (Tree : Project_Tree);
   --  Apply the following rules to each file in [File_List]:
   --    if the file is a body, do nothing;
   --    if the file is a spec, and a body exists, replace by filename of body
   --    if the file is a separate, replace with filename of body
   --  This is required to avoid calling gnat2why on a separate body (will
   --  crash) or on a spec when there is a body (gnat2why will incorrectly
   --  assume that there is no body)

   Usage_Message : constant String :=
     "-Pproj [files] [switches] [-cargs switches]";

   --  Hidden switches: --ide-progress-bar
   Help_Message : constant String :=
"proj is a GNAT project file" &
ASCII.LF &
"files is one or more file names" &
ASCII.LF &
"-cargs switches are passed to gcc" &
ASCII.LF &
ASCII.LF &
"gnatprove basic switches:" & ASCII.LF &
" -f                 Force recompilation/analysis of all units" &
ASCII.LF &
" -jnnn              Use nnn parallel processes (default: 1)" &
ASCII.LF &
" -k                 Do not stop analysis at the first error" &
ASCII.LF &
"     --mode=m       Set the mode of GNATprove (m=check, flow, prove, all*)"
& ASCII.LF &
" -q, --quiet        Be quiet/terse" &
ASCII.LF &
"     --clean        Remove GNATprove intermediate files, and exit" &
ASCII.LF &
"     --report=r     Set the report mode of GNATprove " &
"(r=fail*, all, statistics)"
&
ASCII.LF &
" -u                 Unique compilation, only prove the given files" &
ASCII.LF &
" -U                 Prove all files of all projects" &

ASCII.LF &
" -v, --verbose      Output extra verbose information" &
ASCII.LF &
"     --version      Output version of the tool and exit" &
ASCII.LF &
"     --warnings=w   Set the warning mode of GNATprove " &
"(w=off, on, error*)"
&
ASCII.LF &
" -h, --help         Display this usage information" &
ASCII.LF &
ASCII.LF &
" * Main mode values" &
ASCII.LF &
"   . check - Check SPARK restrictions for code where SPARK_Mode=On" &
ASCII.LF &
"   . flow  - Prove object initialization and flow contracts" &
ASCII.LF &
"   . prove - Prove subprogram contracts and absence of run-time errors" &
ASCII.LF &
"   . all   - Activates all modes (default)" &
ASCII.LF &
ASCII.LF &
" * Report mode values" &
ASCII.LF &
"   . fail       - Report failures to prove checks (default)" &
ASCII.LF &
"   . all        - Report all results of proving checks" &
ASCII.LF &
"   . statistics - Same as all, plus timing and steps information" &
ASCII.LF &
ASCII.LF &
" * Warning mode values" &
ASCII.LF &
"   . off   - Do not issue warnings" &
ASCII.LF &
"   . on    - Issue warnings" &
ASCII.LF &
"   . error - Treat warnings as errors (default)" &
ASCII.LF &
ASCII.LF &
"gnatprove advanced switches:" &
ASCII.LF &
" -d, --debug        Debug mode" &
ASCII.LF &
" --flow-debug       Extra debugging for flow analysis (requires graphviz)" &
ASCII.LF &
"     --proof=p      Set the proof mode (p=no_split*, then_split, path_wp,"&
ASCII.LF &
"                    no_wp, all_split)" &
ASCII.LF &
"     --RTS=dir      Specify the Ada runtime name/location" &
ASCII.LF &
"     --show-tag     Append a unique tag to each error message" &
ASCII.LF &
"     --pedantic     Use a strict interpretation of the Ada standard" &
ASCII.LF &
"     --steps=nnn    Set the maximum number of proof steps to nnn for Alt-Ergo"
& ASCII.LF &
"     --timeout=s    Set the prover timeout in seconds (default: 1)" &
ASCII.LF &
"     --limit-line=s Limit analysis to given file and line" &
ASCII.LF &
"     --limit-subp=s Limit analysis to subprogram defined by file and line" &
  ASCII.LF &
"     --prover=s     Use given prover instead of default Alt-Ergo prover" &
ASCII.LF &
ASCII.LF &
" * Proof mode values" &
ASCII.LF &
"   . no_split   - Generate one formula per check (default)" &
ASCII.LF &
"   . then_split - Start with one formula per check, then split into" &
ASCII.LF &
"                  paths when needed" &
ASCII.LF &
"   . path_wp    - Generate one formula per path for each check" &
ASCII.LF &
"   . no_wp      - Do not compute checks, do not call prover" &
ASCII.LF &
"   . all_split  - Compute all checks, save them to file, do not call prover" &
ASCII.LF;

   --------------
   -- Clean_Up --
   --------------

   procedure Clean_Up (Tree : Project_Tree) is
      Proj_Type : constant Project_Type := Root_Project (Tree);
      Obj_Dir   : constant GNATCOLL.VFS.Virtual_File := Proj_Type.Object_Dir;
   begin
      GNAT.Directory_Operations.Remove_Dir (Obj_Dir.Display_Full_Name, True);
   end Clean_Up;

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
      Section   : String) is
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

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Proof_Mode) return String is
   begin
      case P is
         when No_WP => return "no_wp";
         when All_Split => return "all_split";
         when Then_Split => return "then_split";
         when Path_WP => return "path_wp";
         when No_Split => return "no_split";
      end case;
   end To_String;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project_Tree) is
      Config : Command_Line_Configuration;

      procedure Abort_With_Help (Msg : String)
         with No_Return;
      --  Stop the program, output the message and the help message, then exit

      function Init return Project_Tree;
      --  Load the project file; This function requires the project file to be
      --  present.

      ---------------------
      -- Abort_With_Help --
      ---------------------

      procedure Abort_With_Help (Msg : String) is
      begin
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
         Ada.Text_IO.New_Line;
         Display_Help (Config);
         GNAT.OS_Lib.OS_Exit (1);
      end Abort_With_Help;

      ----------
      -- Init --
      ----------

      function Init return Project_Tree is
         Proj_Env     : Project_Environment_Access;
         GNAT_Version : GNAT.Strings.String_Access;
         Tree         : Project_Tree;

      begin
         Initialize (Proj_Env);
         Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
         Set_Object_Subdir (Proj_Env.all, Subdir_Name);
         Proj_Env.Register_Default_Language_Extension ("C", ".h", ".c");
         declare
            S : constant String :=
                  Register_New_Attribute ("Switches", "Prove",
                                          Is_List => True);
         begin
            if S /= "" then
               Abort_With_Help (S);
            end if;
         end;
         if Project_File.all /= "" then
            Tree.Load
              (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
               Proj_Env);
         else
            Abort_With_Help ("No project file is given, aborting");
         end if;

         return Tree;
      end Init;

      First_Config : Command_Line_Configuration;
      Com_Lin : aliased String_List :=
        (1 .. Ada.Command_Line.Argument_Count => <>);

   begin
      --  We parse the command line *twice*.

      --  First parsing recognizes all switches with "immediate"
      --  behavior that either does not need a project file, or does not need
      --  the extra switches that may be defined in the project file.

      --  We then concatenate the extra switches to the command line and,
      --  reparse the whole thing.

      --  As parsing the command line consumes it, we start by copying it.

      for Index in 1 .. Com_Lin'Last loop
         Com_Lin (Index) :=
           new String'(Ada.Command_Line.Argument (Index));
      end loop;

      --  The first parsing only defines the project file switch, and
      --  immediately terminating switches such as --version and --clean. We
      --  also need a wildcard to ignore the other switches.

      Set_Usage
        (First_Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      Define_Switch
        (First_Config, Project_File'Access,
         "-P:",
         Help => "The name of the project file");

      Define_Switch
        (First_Config,
         Version'Access,
         Long_Switch => "--version",
         Help => "Output version of the tool");

      Define_Switch
         (First_Config,
          Clean'Access,
          Long_Switch => "--clean",
          Help => "Remove GNATprove intermediate files");

      Define_Switch (First_Config, "*", Help => "list of source files");

      Getopt (First_Config,
              Callback => Do_Nothing'Access,
              Concatenate => False);

      if Version then
         Ada.Text_IO.Put_Line (SPARK2014_Version_String);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      --  The second parsing needs the info for all switches

      Set_Usage
        (Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      Define_Switch
         (Config,
          Debug'Access,
          "-d", Long_Switch => "--debug");

      Define_Switch
         (Config,
          Flow_Extra_Debug'Access,
          Long_Switch => "--flow-debug");

      Define_Switch
        (Config, Project_File'Access,
         "-P:");

      Define_Switch
        (Config,
         Force'Access,
         "-f");

      Define_Switch
         (Config, Parallel'Access,
          Long_Switch => "-j:",
          Initial => -1);

      Define_Switch
         (Config,
          Continue_On_Error'Access,
          "-k");

      Define_Switch
        (Config,
         MMode_Input'Access,
         Long_Switch => "--mode=");

      Define_Switch
        (Config,
         Warning_Input'Access,
         Long_Switch => "--warnings=");

      Define_Switch
        (Config,
         Proof_Input'Access,
         Long_Switch => "--proof=");

      Define_Switch
        (Config,
         Pedantic'Access,
         Long_Switch => "--pedantic");

      Define_Switch
        (Config,
         RTS_Dir'Access,
         Long_Switch => "--RTS=");

      Define_Switch
        (Config,
         IDE_Progress_Bar'Access,
         Long_Switch => "--ide-progress-bar");

      Define_Switch
        (Config,
         Show_Tag'Access,
         Long_Switch => "--show-tag");

      Define_Switch
         (Config,
          Quiet'Access,
          "-q", Long_Switch => "--quiet");

      Define_Switch
        (Config,
         Report_Input'Access,
         Long_Switch => "--report=");

      Define_Switch
         (Config, Steps'Access,
          Long_Switch => "--steps=");

      Define_Switch
         (Config, Timeout'Access,
          Long_Switch => "--timeout=");

      Define_Switch
         (Config,
          Only_Given'Access,
          "-u");

      Define_Switch
         (Config,
          All_Projects'Access,
          "-U");

      Define_Switch
        (Config,
         Verbose'Access,
         "-v", Long_Switch => "--verbose");

      Define_Switch
        (Config,
         Limit_Line'Access,
         Long_Switch => "--limit-line=");

      Define_Switch (Config, "*");

      Define_Switch
        (Config,
         Limit_Subp'Access,
         Long_Switch => "--limit-subp=");

      Define_Switch
        (Config,
         Alter_Prover'Access,
         Long_Switch => "--prover=");

      Define_Section (Config, "cargs");
      Define_Switch (Config, "*", Section => "cargs");

      --  Before doing the actual second parsing, we read the project file in

      Tree := Init;

      if Clean then
         Clean_Up (Tree);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

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

      --  Adjust the number of parallel processes. If -j0 was used, the
      --  number of processes should be set to the actual number of
      --  processors available on the machine.

      if Parallel = 0 then
         Parallel := Natural (System.Multiprocessors.Number_Of_CPUs);
      end if;

      if MMode_Input.all = "prove" then
         MMode := GPM_Prove;
      elsif MMode_Input.all = "check" then
         MMode := GPM_Check;
      elsif MMode_Input.all = "flow" then
         MMode := GPM_Flow;
      elsif MMode_Input.all = "all" or else MMode_Input.all = "" then
         MMode := GPM_All;
      else
         Abort_With_Help ("mode should be one of " &
                            "(check | prove | flow | all)");
      end if;

      if Warning_Input.all = "off" then
         Warning_Mode := Opt.Suppress;
      elsif Warning_Input.all = "on" then
         Warning_Mode := Opt.Normal;
      elsif Warning_Input.all = "error" or else Warning_Input.all = "" then
         Warning_Mode := Opt.Treat_As_Error;
      else
         Abort_With_Help ("warnings should be one of (off | on | error)");
      end if;

      if Report_Input.all = "fail" or else Report_Input.all = "" then
         Report := GPR_Fail;
      elsif Report_Input.all = "all" then
         Report := GPR_Verbose;
      elsif Report_Input.all = "statistics" then
         Report := GPR_Statistics;
      else
         Abort_With_Help
           ("report should be one of (fail | all | statistics)");
      end if;

      if Proof_Input.all = "then_split" then
         Proof := Then_Split;
      elsif Proof_Input.all = "no_wp" then
         Proof := No_WP;
      elsif Proof_Input.all = "all_split" then
         Proof := All_Split;
      elsif Proof_Input.all = "path_wp" then
         Proof := Path_WP;
      elsif Proof_Input.all = "no_split" then
         Proof := No_Split;

      --  The default proof mode is no_split

      elsif Proof_Input.all = "" then
         Proof := No_Split;
      else
         Abort_With_Help
           ("proof mode should be one of " &
            "(then_split | no_wp | all_split | path_wp | no_split)");
      end if;

      if Flow_Extra_Debug and not Debug then
         Abort_With_Help ("extra debugging for flow analysis requires -d");
      end if;

      declare
         Limit_String : GNAT.Strings.String_Access := null;
      begin

         --  Limit_Line and Limit_Subp both imply -u for the corresponding
         --  file. We take care of that using the Limit_String variable, note
         --  that "Limit_Line" is stronger naturally.

         if Limit_Subp /= null and then Limit_Subp.all /= "" then
            Limit_String := Limit_Subp;
         end if;

         if Limit_Line /= null and then Limit_Line.all /= "" then
            Limit_String := Limit_Line;
         end if;

         if Limit_String /= null then
            declare
               Index : Integer := Limit_String.all'Last;
            begin
               while Index > Limit_String.all'First and then
                 Limit_String.all (Index) /= ':' loop
                  Index := Index - 1;
               end loop;
               if Index = Limit_String.all'First then
                  Abort_With_Message
                    ("limit-line: incorrect line specification - missing ':'");
               end if;
               File_List.Append
                 (Limit_String.all (Limit_String.all'First .. Index - 1));
            end;
            Only_Given := True;
         end if;
      end;

      Sanitize_File_List (Tree);

   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
      when Invalid_Parameter =>
         Abort_With_Help ("No parameter given to switch -" & Full_Switch);
   end Read_Command_Line;

   ------------------------
   -- Sanitize_File_List --
   ------------------------

   procedure Sanitize_File_List (Tree : Project_Tree) is
      use String_Lists;
   begin
      for Cursor in File_List.Iterate loop
         declare
            File_VF : constant Virtual_File :=
              Create_From_Base (Filesystem_String (Element (Cursor)));
            Info    : constant File_Info := Tree.Info (File_VF);
         begin
            case Unit_Part (Info) is
            when Unit_Body =>
               null;
            when Unit_Spec =>
               declare
                  Other_VF : constant Virtual_File :=
                    Tree.Other_File (File_VF);
               begin
                  if Is_Regular_File (Other_VF) then
                     File_List.Replace_Element
                       (Cursor,
                        String (Base_Name (Other_VF)));
                  end if;
               end;
               when Unit_Separate =>
                  declare
                     Ptype : constant Project_Type := Tree.Root_Project;
                     Other_VF : Virtual_File;
                  begin
                     Other_VF :=
                       Create_From_Base
                         (Ptype.File_From_Unit (Unit_Name (Info),
                          Unit_Body,
                          "Ada"));
                     File_List.Replace_Element
                       (Cursor,
                        String (Base_Name (Other_VF)));
                  end;
            end case;
         end;
      end loop;
   end Sanitize_File_List;

   -----------------------
   -- SPARK_Report_File --
   -----------------------

   function SPARK_Report_File (Out_Dir : String) return String is
   begin
      return Ada.Directories.Compose (Out_Dir, "gnatprove.out");
   end SPARK_Report_File;

end Configuration;
