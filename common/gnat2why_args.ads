------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y _ A R G S                       --
--                                                                          --
--                                 S p e c                                  --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Opt;
with String_Utils;          use String_Utils;

package Gnat2Why_Args is

   --  This unit defines and initializes extra options of gnat2why, that are
   --  not relevant to the GNAT frontend.

   --  These package defines both the reading and the writing of these extra
   --  options. There are two ways to use this package, depending on whether
   --  you are on the reading side (gnat2why) or the writing side (gnatprove).

   --  For reading the extra options, simply call "init". Now the global
   --  variables defined at the beginning of this package are set corresponding
   --  to the extra options.

   --  For writing extra options, set the global variables to the required
   --  values, and call "Set".

   --  These extra options are stored in a file that is passed to gnat2why
   --  using the extra switch "-gnates=<file>". See the body of this package
   --  for the format of this file, the spec only describes what is needed for
   --  interfacing.

   -------------------------------------
   -- Options defined in this package --
   -------------------------------------

   --  Warning mode for gnat2why. This is similar to Opt.Warning_Mode for
   --  the compiler.

   Warning_Mode : Opt.Warning_Mode_Type := Opt.Treat_As_Error;

   --  Global generation mode. In this mode, gnat2why generates cross-reference
   --  information in ALI files for being able to generated the globals read
   --  and writen by subprograms.

   Global_Gen_Mode : Boolean := False;

   --  SPARK 2014 checking mode. In this mode, gnat2why checks that sections of
   --  code marked as SPARK_Mode=>True do not contain violations of SPARK 2014.

   Check_Mode : Boolean := False;

   --  Flow Analysis mode. In this mode, gnat2why will do flow analysis, in
   --  addition to translation to Why.

   Flow_Analysis_Mode : Boolean := False;

   --  Enable basic debugging for flow analysis. This will dump the
   --  CFG and PDG is dot format.

   Flow_Debug_Mode : Boolean := False;

   --  This will enable additional tracing output and will call
   --  graphviz on each dumped graph.

   Flow_Advanced_Debug : Boolean := False;

   --  When Pedantic is True, issue warnings on features that could cause
   --  portability issues with other compilers than GNAT. For example, issue
   --  a warning when the Ada RM allows reassociation of operators in an
   --  expression (something GNAT never does), which could lead to different
   --  overflows, e.g. on
   --    A + B + C
   --  which is parsed as
   --    (A + B) + C
   --  but could be reassociated by another compiler as
   --    A + (B + C)

   Pedantic : Boolean := False;

   --  If this list is non-empty, only units of this list should be analyzed.

   Analyze_File : String_Lists.List := String_Lists.Empty_List;

   --  Limit analysis to this subprogram

   Limit_Subp   : Unbounded_String := Null_Unbounded_String;

   --  IDE mode. Error messages may be formatted differently in this mode (e.g.
   --  JSON dict)

   Ide_Mode : Boolean := False;

   --------------------------------
   -- Procedures of this package --
   --------------------------------

   procedure Init;
   --  Read the extra options information and set the corresponding global
   --  variables above.

   function Set (Obj_Dir : String) return String;
   --  Read the above variables and prepare passing them to gnat2why. Obj_Dir
   --  is a place to store temp files, and the return value is the full name
   --  of the file that is to be passed to gnat2why using -gnates=<file>.

end Gnat2Why_Args;
