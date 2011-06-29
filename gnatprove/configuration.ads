------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;

with GNAT.Strings;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.Utils;    use GNATCOLL.Utils;
with GNATCOLL.VFS;      use GNATCOLL.VFS;

package Configuration is
   Verbose      : aliased Boolean;
   --  True if -v switch is present. All executed commands are printed.
   Force        : aliased Boolean;
   --  True if -f is present. Force recompilation of all units.
   Quiet        : aliased Boolean;
   --  True if -q is present. Do not print on standard output.
   Debug        : aliased Boolean;
   --  True if -d is present. Do not remove temporary files.

   type GP_Mode is (GPM_Detect, GPM_Force, GPM_Check, GPM_Prove);

   Mode         : GP_Mode := GPM_Detect;
   Mode_Input   : aliased GNAT.Strings.String_Access;
   --  The mode of gnatprove, and the input variable for command line parsing
   --  set by option --mode=
   Report_Input   : aliased GNAT.Strings.String_Access;
   --  The input variable for command line parsing set by option --report=
   Report      : aliased Boolean;
   --  True is --report=all is present. Give messages even for proved VCs
   No_Proof     : aliased Boolean;
   --  True if --no-proof switch is present. Do not call Alt-Ergo.
   Parallel     : aliased Integer;
   --  The number of parallel processes. Specified with -j.
   Timeout      : aliased Integer;
   --  The number of seconds to try to prove each VC. Specified with
   --  --timeout=.
   Steps        : aliased Integer;
   --  The number of steps to try to prove each VC. Specified with --steps=.
   Project_File : aliased GNAT.Strings.String_Access;
   --  The project file name, given with option -P

   Subdir_Name  : constant Filesystem_String := "gnatprove";
   --  The name of the directory in which all work takes place
   Prefix       : constant String := Executable_Location;
   --  The prefix directory of the gnatprove installation
   Lib_Dir      : constant String := Ada.Directories.Compose (Prefix, "lib");
   --  <prefix>/lib
   Why_Lib_Dir  : constant String := Ada.Directories.Compose (Lib_Dir, "why");
   --  <prefix>/lib/why - the default Why library dir
   Stdlib_ALI_Dir   : constant String :=
      Ada.Directories.Compose (Lib_Dir, "gnatprove");
   --  <prefix>/lib/gnatprove, used to store the ALI files of the stdlib
   Gpr_Cnf_Dir  : constant String :=
      Ada.Directories.Compose
        (Ada.Directories.Compose (Prefix, "share"),
         "gnatprove");
   --  <prefix>/share/gnatprove, used to store gprbuild configuration files
   --  used by gnatprove
   Gpr_Ada_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "gnat2why.cgpr");
   Gpr_Why_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "why.cgpr");
   Gpr_Altergo_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "altergo.cgpr");
   --  The exact places for the three configuration files used by gnatprove

   WHYLIB       : constant String := "WHYLIB";
   --  The name of the environment variable which can be used to set the
   --  library directory of Why
   Alfa_Report_File : constant String := "gnatprove.out";
   --  The name of the file in which the Alfa report is generated

   Alfa_Suffix    : constant String := ".alfa";
   --  Suffix for raw Alfa information files

   procedure Init (Tree : out Project_Tree);
   --  Initialize the project tree.

end Configuration;
