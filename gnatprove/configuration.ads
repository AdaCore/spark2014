------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
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

with Ada.Directories;

with GNAT.Strings;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.Utils;    use GNATCOLL.Utils;
with GNATCOLL.VFS;      use GNATCOLL.VFS;
with String_Utils;      use String_Utils;

package Configuration is

   Max_Non_Blank_Lines : constant := 6;
   --  Maximum number of consecutive non blank lines on standard output

   Label_Length : constant := 26;
   --  Maximum length of label in report. Other characters are discarded.

   Version      : aliased Boolean;
   --  True if --version switch is present. Output current version and exit.
   Verbose      : aliased Boolean;
   --  True if -v switch is present. All executed commands are printed.
   Force        : aliased Boolean;
   --  True if -f is present. Force recompilation of all units.
   Quiet        : aliased Boolean;
   --  True if -q is present. Do not print on standard output.
   Debug        : aliased Boolean;
   --  True if -d is present. Do not remove temporary files.
   Only_Given   : aliased Boolean;
   --  True if -u is present. Only compile/prove given files
   All_Projects : aliased Boolean;
   --  True if -U is present. compile/prove all files of all projects
   Pedantic     : aliased Boolean;
   --  True if --strict switch is present. Stricter interpretation of language.
   IDE_Progress_Bar : aliased Boolean;
   --  True if --ide-progress-bar switch is present. Generate information on
   --  progress for display in IDE.
   Show_Tag     : aliased Boolean;
   --  True if --show_tag switch is present. Add a unique tag to each error
   --  message.
   Limit_Line   : aliased GNAT.Strings.String_Access;
   --  Set to non-empty string when option --limit-line= was given
   Limit_Subp   : aliased GNAT.Strings.String_Access;
   --  Set to non-empty string when option --limit-subp= was given
   Alter_Prover : aliased GNAT.Strings.String_Access;
   --  Set to non-empty string when option --prover= was given

   type GP_Mode is (GPM_Check, GPM_Flow, GPM_Prove, GPM_All);
   --  The four feature modes of GNATprove:
   --  * GPM_Check  : Check SPARK rules
   --  * GPM_Prove  : Check validity of contracts, proof of subprogram bodies
   --  * GPM_Flow   : Check validity of Globals, Depends
   --  * GPM_All    : Union of GPM_Prove and GPM_Flow

   type Report_Mode is (GPR_Fail, GPR_Verbose, GPR_Statistics);
   --  The modes for reporting of VCs.
   --    GPR_Fail means that only unproved VCs will be reported.
   --    GPR_Verbose means that all VCs will be reported
   --    GPR_Statistics means that all VCs will be reported, plus steps and
   --    timing information.

   type Proof_Mode is (Then_Split, No_WP, All_Split, Path_WP, No_Split);
   --  This is a debug option of GNATprove. This option is simply passed to
   --  gnatwhy3.
   --  The modes for proof are:
   --  Then_Split: compute WP, split VCs as necessary, call prover as necessary
   --  No_WP: do not compute WP, do not split VCs, do not call prover
   --  All_Split: compute VCs, split all VCs, do not call prover
   --  Path_WP: use the "normal" (exponential) WP
   --  No_Split: only use fast WP, no split of VCs at all

   MMode        : GP_Mode := GPM_Prove;
   Report       : Report_Mode := GPR_Fail;
   --  Silent reporting is the default
   Proof        : Proof_Mode;
   --  The default proof mode depends on other switches
   Parallel     : aliased Integer;
   --  The number of parallel processes. Specified with -j.
   Timeout      : aliased Integer;
   --  The number of seconds to try to prove each VC. Specified with
   --  --timeout=.
   Steps        : aliased Integer;
   --  The number of steps to try to prove each VC. Specified with --steps=.
   Project_File : aliased GNAT.Strings.String_Access;
   --  The project file name, given with option -P
   File_List    : String_Lists.List;
   --  The list of files to be compiled

   Cargs_List   : String_Lists.List;
   --  The options to be passed to the compilers

   Subdir_Name  : constant Filesystem_String := "gnatprove";
   --  The name of the directory in which all work takes place

   --  Here we set the various paths that are needed during a run of
   --  gnatprove. The hierarchy looks as follows:
   --  prefix
   --  prefix/lib
   --  prefix/lib/gnatprove   -     ALI files of the stdlib
   --  prefix/share
   --  prefix/share/why3      -     files that come with Why3
   --  prefix/share/gnatprove/config - gprbuild config files
   --  prefix/share/gnatprove/stdlib - Why3 files of the stdlib
   --  prefix/share/gnatprove/theories - Why3 files for Ada theories
   --
   Prefix         : constant String := Executable_Location;
   Lib_Dir        : constant String :=
      Ada.Directories.Compose (Prefix, "lib");
   Stdlib_ALI_Dir : constant String :=
      Ada.Directories.Compose (Lib_Dir, "gnatprove");
   Share_Dir      : constant String :=
      Ada.Directories.Compose (Prefix, "share");
   Why3_Dir       : constant String :=
      Ada.Directories.Compose (Share_Dir, "why3");
   Gnatprove_Dir  : constant String :=
      Ada.Directories.Compose (Share_Dir, "gnatprove");
   Theories_Dir   : constant String :=
      Ada.Directories.Compose (Gnatprove_Dir, "theories");
   Gpr_Cnf_Dir    : constant String :=
      Ada.Directories.Compose (Gnatprove_Dir, "config");

   Stdlib_Dir     : constant String :=
      Ada.Directories.Compose (Gnatprove_Dir, "stdlib");

   Why3_Drivers_Dir : constant String :=
      Ada.Directories.Compose (Why3_Dir, "drivers");

   --  The exact places for the three configuration files used by gnatprove
   Gpr_Translataion_Cnf_File : constant String :=
     Ada.Directories.Compose (Gpr_Cnf_Dir, "gnat2why.cgpr");
   Gpr_Frames_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "frames.cgpr");
   Gpr_Why_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "why.cgpr");

   function SPARK_Report_File (Out_Dir : String) return String;
   --  The name of the file in which the SPARK report is generated:
   --    Out_Dir/gnatprove.out

   SPARK_Suffix : constant String := ".alfa";
   --  Suffix for raw SPARK information files

   procedure Read_Command_Line (Tree : out Project_Tree);

   function To_String (P : Proof_Mode) return String;
   --  transform the proof mode into a string for gnatwhy3 command line option
end Configuration;
