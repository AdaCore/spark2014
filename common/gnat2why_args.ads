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

package Gnat2Why_Args is

   --  This unit defines and initializes extra options of gnat2why, that are
   --  not relevant to the GNAT frontend.

   --  Today, these options are read from the environment variable
   --  GNAT2WHY_ARGS. This variable contains a list of tokens. Each token has
   --  the same name in lower case as the corresponding variable in this
   --  package.

   --  Reading in the environment variable is done by a call to [Init].

   --  Setting the environment variable is done by changing the values of the
   --  variables and calling [Set].

   -------------------------------------
   -- Options defined in this package --
   -------------------------------------

   --  Standard package only mode. In this mode, gnat2why will only generate
   --  Why code for package Standard. Any given input file will be ignored.

   Standard_Mode : Boolean := False;

   --  SPARK check mode. In this mode, gnat2why does not generate Why code.

   Check_Mode : Boolean := False;

   --  Flow Analysis mode. In this mode, gnat2why will do flow analysis, in
   --  addition to translation to Why.

   Flow_Analysis_Mode : Boolean := False;

   --  Flow analysis mode (-gnatd.Q), dump the different graphs (control flow,
   --  control dependence) for debugging purposes.

   Flow_Dump_Graphs : Boolean := False;

   --  If this string is non-empty, only this unit should be analyzed.

   Analyze_File : Unbounded_String := Null_Unbounded_String;

   --------------------------------
   -- Procedures of this package --
   --------------------------------

   procedure Init;
   --  Read the environment variable GNAT2WHY_Args and set the corresponding
   --  options.

   procedure Set;
   --  Read the above variables and set the environment variable

   procedure Clear;
   --  Clear the environment variable, do not change the variables.

end Gnat2Why_Args;
