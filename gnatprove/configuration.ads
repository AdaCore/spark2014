------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Ada.Containers.Indefinite_Hashed_Sets;
with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Directories;   use Ada.Directories;
with Ada.Strings.Hash;
with Call;              use Call;
with GNAT.Strings;
with Gnat2Why_Opts;     use Gnat2Why_Opts;
with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.Utils;    use GNATCOLL.Utils;
with GNATCOLL.VFS;      use GNATCOLL.VFS;
with Named_Semaphores;  use Named_Semaphores;
with String_Utils;      use String_Utils;

package Configuration is

   package Dir_Name_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (Element_Type        => String,
      Hash                => Ada.Strings.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Constants is
      --  This package contains constants that influence the behavior of
      --  gnatprove.

      Max_CE_Timeout : constant Integer := 10;
      --  ???

   end Constants;

   package CL_Switches is

      --  These are the variables that contain the values of the corresponding
      --  switches of gnatprove. Note that these correspond exactly to the
      --  commandline as given by the user. If some postprocessing is applied
      --  to the switch (for example timeout, steps etc are influenced by the
      --  level switch) another variable is introduced outside of this package.
      --  Naming of the variable:
      --  * single letter variables correspond to single letter switches with
      --    one dash, like -j, -v
      --  * variable UU corresponds to -U
      --  * other variables are with two dashes, e.g. --codepeer
      --  * File_List stands for the file arguments (that are not arguments of
      --    some switch)
      --  * Cargs_List is the list of arguments in the --cargs section

      Assumptions          : aliased Boolean;
      Benchmark            : aliased Boolean;
      Memcached_Server     : aliased GNAT.Strings.String_Access;
      Cargs_List           : String_Lists.List;
      Checks_As_Errors     : aliased Boolean;
      CodePeer             : aliased GNAT.Strings.String_Access;
      Coverage             : aliased Boolean;
      CWE                  : aliased Boolean;
      D                    : aliased Boolean;
      Dbg_No_Sem           : aliased Boolean;
      --  disable use of semaphores for ease of debugging
      Debug_Save_VCs       : aliased Boolean;
      Debug_Trivial        : aliased Boolean;
      Dbg_Proof_Only       : aliased Boolean;
      F                    : aliased Boolean;
      File_List            : String_Lists.List;
      --  The list of files to be compiled
      Flow_Debug           : aliased Boolean;
      Flow_Termination     : aliased Boolean;
      Flow_Show_GG         : aliased Boolean;
      GPR_Project_Path     : String_Lists.List;
      --  extra paths to look for project files, passed to gnatprove via -aP
      IDE_Progress_Bar     : aliased Boolean;
      Info                 : aliased Boolean;
      J                    : aliased Integer;
      K                    : aliased Boolean;
      Level                : aliased Integer;
      Limit_Line           : aliased GNAT.Strings.String_Access;
      Limit_Region         : aliased GNAT.Strings.String_Access;
      Limit_Subp           : aliased GNAT.Strings.String_Access;
      List_Categories      : aliased Boolean;
      M                    : aliased Boolean;
      Memlimit             : aliased Integer;
      Mode                 : aliased GNAT.Strings.String_Access;
      No_Axiom_Guard       : aliased Boolean;
      No_Counterexample    : aliased Boolean;
      No_Inlining          : aliased Boolean;
      No_Loop_Unrolling    : aliased Boolean;
      No_Global_Generation : aliased Boolean;
      No_Subprojects       : aliased Boolean;
      Output_Header        : aliased Boolean;
      Output_Msg_Only      : aliased Boolean;
      P                    : aliased GNAT.Strings.String_Access;
      --  The project file name, given with option -P
      Pedantic             : aliased Boolean;
      Proof                : aliased GNAT.Strings.String_Access;
      Proof_Warnings       : aliased Boolean;
      Prover               : aliased GNAT.Strings.String_Access;
      Q                    : aliased Boolean;
      Replay               : aliased Boolean;
      Report               : aliased GNAT.Strings.String_Access;
      RTS                  : aliased GNAT.Strings.String_Access;
      Steps                : aliased Integer;
      Subdirs              : aliased GNAT.Strings.String_Access;
      Target               : aliased GNAT.Strings.String_Access;
      Timeout              : aliased GNAT.Strings.String_Access;
      U                    : aliased Boolean;
      UU                   : aliased Boolean;
      V                    : aliased Boolean;
      Version              : aliased Boolean;
      Warnings             : aliased GNAT.Strings.String_Access;
      Why3_Conf            : aliased GNAT.Strings.String_Access;
      Why3_Debug           : aliased GNAT.Strings.String_Access;
      X                    : String_Lists.List;
      --  Scenario variables to be passed to gprbuild
      Z3_Counterexample    : aliased Boolean;
   end CL_Switches;

   package Prj_Attr is

      --  The attributes of the project file that are accessed by gnatprove.
      --  This does not include the "Prove.Switches" attribute, which is
      --  considered to be part of the command line.

      Runtime : GNAT.Strings.String_Access;
      Target  : GNAT.Strings.String_Access;

      package Builder is
         Global_Compilation_Switches_Ada : GNAT.Strings.String_List_Access;
      end Builder;

      package Prove is
         Proof_Dir              : GNAT.Strings.String_Access;
         Switches               : GNAT.Strings.String_List_Access;
         Proof_Switches_Ada     : GNAT.Strings.String_List_Access;
         Proof_Switches_Indices : GNAT.Strings.String_List_Access;

         function Proof_Switches (Proj : Project_Type; Index : String)
                                  return GNAT.Strings.String_List_Access;
      end Prove;
   end Prj_Attr;

   type GP_Mode is (GPM_Check, GPM_Check_All, GPM_Flow, GPM_Prove, GPM_All);
   --  The feature modes of GNATprove are:
   --  * GPM_Check     : Check SPARK rules
   --  * GPM_Check_All : Check all SPARK rules, including the ones checked
   --                    during flow analysis.
   --  * GPM_Prove     : Check validity of contracts, proof of subprogram
   --                    bodies.
   --  * GPM_Flow      : Check validity of Globals, Depends
   --  * GPM_All       : Union of GPM_Prove and GPM_Flow

   type Proof_Mode is (Progressive, No_WP, All_Split, Per_Path, Per_Check);

   --  Attributes that are synthesized from the command line and project file.
   --  They are either defined in the Postprocess procedure or are simple
   --  renamings of the command line switches (for them we still prefer to
   --  use a clearer name, e.g. Continue_On_Error vs K).

   CodePeer       : Boolean;
   Counterexample : Boolean;
   Debug          : Boolean;
   GnateT_Switch  : GNAT.Strings.String_Access;
   Mode           : GP_Mode;
   Only_Given     : Boolean;
   Parallel       : Integer;
   Report         : Report_Mode_Type;
   Warning_Mode   : Gnat2Why_Opts.SPARK_Warning_Mode_Type;

   All_Projects      : Boolean renames CL_Switches.UU;
   Continue_On_Error : Boolean renames CL_Switches.K;
   Flow_Extra_Debug  : Boolean renames CL_Switches.Flow_Debug;
   Force             : Boolean renames CL_Switches.F;
   IDE_Mode          : Boolean renames CL_Switches.IDE_Progress_Bar;
   Minimal_Compile   : Boolean renames CL_Switches.M;
   Quiet             : Boolean renames CL_Switches.Q;
   Verbose           : Boolean renames CL_Switches.V;

   type File_Specific is record
      Proof             : Proof_Mode;
      Lazy              : Boolean;
      Provers           : String_Lists.List;
      Timeout           : Integer;
      Steps             : Integer;
      Memlimit          : Integer;
      CE_Timeout        : Integer;
      No_Inlining       : Boolean;
      Info              : Boolean;
      No_Loop_Unrolling : Boolean;
      Proof_Warnings    : Boolean;
   end record;

   package File_Specific_Maps is new Ada.Containers.Indefinite_Hashed_Maps
     (Key_Type        => String,
      Element_Type    => File_Specific,
      Hash            => Ada.Strings.Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   File_Specific_Map : File_Specific_Maps.Map;

   Max_Non_Blank_Lines : constant := 6;
   --  Maximum number of consecutive non blank lines on standard output

   package SPARK_Install is
         use GNAT.Strings;

         --  Here we set the various paths that are needed during a run of
         --  gnatprove. The hierarchy looks as follows:
         --  prefix
         --  prefix/lib
         --  prefix/libexec/spark
         --  prefix/libexec/spark/bin      - all auxiliary binaries,
         --                                  e.g. gprbuild
         --  prefix/share
         --  prefix/share/why3             - files that come with Why3
         --  prefix/share/spark/config     - various config files
         --  prefix/share/spark/stdlib     - Why3 files of the stdlib
         --  prefix/share/spark/theories   - Why3 files for Ada theories

         Prefix                   : constant String := Executable_Location;
         Lib                      : constant String := Compose (Prefix, "lib");
         Libexec_Spark            : constant String :=
           Compose (Compose (Prefix, "libexec"), "spark");
         Libexec_Spark_Bin        : constant String :=
           Compose (Libexec_Spark, "bin");
         Share                    : constant String :=
           Compose (Prefix, "share");
         Libexec_Share_Why3       : constant String :=
           Compose (Compose (Libexec_Spark, "share"), "why3");
         Share_Spark              : constant String :=
           Compose (Share, "spark");
         Share_Spark_Theories     : constant String :=
           Compose (Share_Spark, "theories");
         Share_Spark_Config       : constant String :=
           Compose (Share_Spark, "config");
         Share_Spark_Runtimes     : constant String :=
           Compose (Share_Spark, "runtimes");
         Help_Msg_File            : constant String :=
           Compose (Share_Spark, "help.txt");
         Gpr_Frames_DB            : constant String :=
           Compose (Share_Spark_Config, "frames");
         Gpr_Translation_DB : constant String :=
           Compose (Share_Spark_Config, "gnat2why");
         Gpr_Frames_Cov_DB        : constant String :=
           Compose (Share_Spark_Config, "frames_coverage");
         Gpr_Gnat2why_Cov_DB     : constant String :=
           Compose (Share_Spark_Config, "gnat2why_coverage");
         Gnatprove_Conf           : constant String :=
           Compose (Share_Spark_Config, "gnatprove.conf");
         Z3_Present               : Boolean;
         CVC4_Present             : Boolean;
         Help_Message             : constant String :=
           Read_File_Into_String (Help_Msg_File);
   end SPARK_Install;

   Label_Length : constant := 26;
   --  Maximum length of label in report. Other characters are discarded

   Default_Steps : constant Natural := 100;

   Phase1_Subdir : constant Virtual_File := Create ("phase1");
   Phase2_Subdir : Virtual_File := Create ("gnatprove");
   --  The subdir names for the storage of intermediate files (ALI, why3 files,
   --  etc). This is the subdir of the object dir, which might be further
   --  modified via the --subdirs switch. Overall, phase 2 will store files in
   --    <objdir>/<subdirs>/gnatprove
   --  and phase 1 will store files in
   --    <objdir>/<subdirs>/gnatprove/phase1
   --  The fact that the phase 1 dir is a subdir of phase2 makes copying files
   --  easier later on, and makes cleaning up easier as well.

   Proof_Dir : GNAT.Strings.String_Access := null;
   --  The name of the directory in which will be stored Why3 session file and
   --  manual proof files (Attribute of gpr package Prove).

   --  The name of a why3 configuration file to be used in a single run of
   --  gnatprove.

   Socket_Name : GNAT.Strings.String_Access;
   --  Name of the socket used by why3server, based on a hash of the main
   --  object directory.

   Why3_Semaphore : Semaphore;
   --  Name of the named semaphore used to synchronize spawned gnatwhy3
   --  processes.

   function SPARK_Report_File (Out_Dir : String) return String;
   --  The name of the file in which the SPARK report is generated:
   --    Out_Dir/gnatprove.out

   procedure Read_Command_Line (Tree : out Project_Tree);

   function Is_Manual_Prover return Boolean;
   --  @return True iff the alternate prover is "coq" or "isabelle"

   function To_String (P : Proof_Mode) return String;
   --  transform the proof mode into a string for gnatwhy3 command line option

   function Prover_List (Source_File : String) return String;
   function Prover_List (FS : File_Specific) return String;

   function Compute_Why3_Args (Obj_Dir : String;
                               FS      : File_Specific)
                               return String_Lists.List;
   --  Compute the list of arguments of gnatwhy3. This list is passed first to
   --  gnat2why, which then passes it to gnatwhy3.

end Configuration;
