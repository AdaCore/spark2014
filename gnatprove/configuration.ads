------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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
with Ada.Directories;   use Ada.Directories;
with Ada.Strings.Hash;
with GNAT.Strings;
with Gnat2Why_Args;     use Gnat2Why_Args;
with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.Utils;    use GNATCOLL.Utils;
with GNATCOLL.VFS;      use GNATCOLL.VFS;
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
      --  switches of gnatprove:
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
      CodePeer             : aliased GNAT.Strings.String_Access;
      Coverage             : aliased Boolean;
      D                    : aliased Boolean;
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
      J                    : aliased Integer;
      K                    : aliased Boolean;
      Level                : aliased Integer;
      Limit_Line           : aliased GNAT.Strings.String_Access;
      Limit_Subp           : aliased GNAT.Strings.String_Access;
      M                    : aliased Boolean;
      Mode                 : aliased GNAT.Strings.String_Access;
      No_Axiom_Guard       : aliased Boolean;
      No_Counterexample    : aliased Boolean;
      Z3_Counterexample    : aliased Boolean;
      No_Inlining          : aliased Boolean;
      No_Loop_Unrolling    : aliased Boolean;
      No_Global_Generation : aliased Boolean;
      Output_Header        : aliased Boolean;
      Output_Msg_Only      : aliased Boolean;
      P                    : aliased GNAT.Strings.String_Access;
      --  The project file name, given with option -P
      Pedantic             : aliased Boolean;
      Proof                : aliased GNAT.Strings.String_Access;
      Prover               : aliased GNAT.Strings.String_Access;
      Q                    : aliased Boolean;
      Replay               : aliased Boolean;
      Report               : aliased GNAT.Strings.String_Access;
      RTS                  : aliased GNAT.Strings.String_Access;
      Steps                : aliased Integer;
      Timeout              : aliased GNAT.Strings.String_Access;
      U                    : aliased Boolean;
      UU                   : aliased Boolean;
      V                    : aliased Boolean;
      Version              : aliased Boolean;
      Warnings             : aliased GNAT.Strings.String_Access;
      Why3_Conf            : aliased GNAT.Strings.String_Access;
      X                    : String_Lists.List;
      --  Scenario variables to be passed to gprbuild
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
         Proof_Dir : GNAT.Strings.String_Access;
      end Prove;
   end Prj_Attr;

   type GP_Mode is (GPM_Check, GPM_Check_All, GPM_Flow, GPM_Prove, GPM_All);
   --  The four feature modes of GNATprove:
   --  * GPM_Check     : Check SPARK rules
   --  * GPM_Check_All : Check all SPARK rules, including the ones checked
   --                    during flow analysis.
   --  * GPM_Prove     : Check validity of contracts, proof of subprogram
   --                    bodies.
   --  * GPM_Flow      : Check validity of Globals, Depends
   --  * GPM_All       : Union of GPM_Prove and GPM_Flow

   type Proof_Mode is (Progressive, No_WP, All_Split, Per_Path, Per_Check);

   --  The variables that govern behavior of gnatprove. Many of them directly
   --  correspond to a command line switch, but not all. See the Postprocess
   --  function which links variables and switches.

   Verbose              : Boolean;
   Quiet                : Boolean;
   Debug                : Boolean;
   Force                : Boolean;
   Minimal_Compile      : Boolean;
   Flow_Extra_Debug     : Boolean;
   Flow_Termination     : Boolean;
   Flow_Show_GG         : Boolean;
   Continue_On_Error    : Boolean;
   All_Projects         : Boolean;
   IDE_Mode             : Boolean;
   Limit_Line           : GNAT.Strings.String_Access;
   Limit_Subp           : GNAT.Strings.String_Access;
   Only_Given           : Boolean;
   CodePeer             : Boolean;
   RTS_Dir              : GNAT.Strings.String_Access;
   Counterexample       : Boolean;
   No_Axiom_Guard       : Boolean;
   Z3_Counterexample    : Boolean;
   No_Inlining          : Boolean;
   No_Global_Generation : Boolean;
   Mode                 : GP_Mode;
   Warning_Mode         : Gnat2Why_Args.SPARK_Warning_Mode_Type;
   Memcached_Server     : GNAT.Strings.String_Access;
   --  enable caching through memcached
   Report               : Report_Mode_Type;
   Proof                : Proof_Mode;
   Lazy                 : Boolean;
   Parallel             : Integer;
   Provers              : String_Lists.List;
   Timeout              : Integer;
   Steps                : Integer;
   Why3_Config_File     : GNAT.Strings.String_Access;
   CE_Timeout           : Integer;

   Max_Non_Blank_Lines : constant := 6;
   --  Maximum number of consecutive non blank lines on standard output

   package File_System is
      package Install is
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
         Share_Why3               : constant String :=
           Compose (Share, "why3");
         Share_Spark              : constant String :=
           Compose (Share, "spark");
         Share_Spark_Theories     : constant String :=
           Compose (Share_Spark, "theories");
         Share_Spark_Config       : constant String :=
           Compose (Share_Spark, "config");
         Share_Why3_Drivers       : constant String :=
           Compose (Share_Why3, "drivers");
         Share_Spark_Runtimes     : constant String :=
           Compose (Share_Spark, "runtimes");
         Help_Msg_File : constant String :=
           Compose (Share_Spark, "help.txt");
         Frames_Cgpr              : constant String := "frames.cgpr";
         Gnat2why_Cgpr            : constant String := "gnat2why.cgpr";
         Frames_Cov_Cgpr          : constant String := "frames_coverage.cgpr";
         Gnat2why_Cov_Cgpr        : constant String :=
           "gnat2why_coverage.cgpr";
         Gpr_Frames_Cnf_File      : constant String :=
           Compose (Share_Spark_Config, Frames_Cgpr);
         Gpr_Translation_Cnf_File : constant String :=
           Compose (Share_Spark_Config, Gnat2why_Cgpr);
         Gpr_Frames_Cov_Cnf_File  : constant String :=
           Compose (Share_Spark_Config, Frames_Cov_Cgpr);
         Gpr_Gnat2why_Cov_Cnf_File  : constant String :=
           Compose (Share_Spark_Config, Gnat2why_Cov_Cgpr);
         Gnatprove_Conf           : constant String :=
           Compose (Share_Spark_Config, "gnatprove.conf");
         Z3_Present               : Boolean;
         CVC4_Present             : Boolean;
      end Install;
   end File_System;

   Label_Length : constant := 26;
   --  Maximum length of label in report. Other characters are discarded

   Default_Steps : constant Natural := 100;

   Subdir_Name : constant Filesystem_String := "gnatprove";
   --  The name of the directory in which all work takes place

   Main_Subdir : GNAT.Strings.String_Access := null;
   --  The name of the main sub-directory "gnatprove" in which files are
   --  generated. This is the same as
   --  <obj-dir-for-the-main-project>/Subdir_Name

   Proof_Dir : GNAT.Strings.String_Access := null;
   --  The name of the directory in which will be stored Why3 session file and
   --  manual proof files (Attribute of gpr package Prove).

   --  The name of a why3 configuration file to be used in a single run of
   --  gnatprove.

   Socket_Name : GNAT.Strings.String_Access := null;
   --  Name of the socket used by why3server, based on a hash of the main
   --  object directory.

   function SPARK_Report_File (Out_Dir : String) return String;
   --  The name of the file in which the SPARK report is generated:
   --    Out_Dir/gnatprove.out

   procedure Read_Command_Line (Tree : out Project_Tree);

   function Is_Manual_Prover return Boolean;
   --  @return True iff the alternate prover is "coq" or "isabelle"

   function To_String (P : Proof_Mode) return String;
   --  transform the proof mode into a string for gnatwhy3 command line option

   function Prover_List return String
   with Pre => not Provers.Is_Empty;
   --  return comma-separated list of provers
end Configuration;
