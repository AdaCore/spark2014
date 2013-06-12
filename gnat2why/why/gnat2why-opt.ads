------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y - O P T                         --
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

package Gnat2Why.Opt is

   --  This unit defines and initializes extra options of gnat2why, that are
   --  not relevant to the GNAT frontend.

   --  Today, these options are read from the environment variable
   --  GNAT2WHY_ARGS. This variable contains a list of tokens. Each token has
   --  the same name in lower case as the corresponding variable in this
   --  package.

   --  Reading in the environment variable is done by a call to [Init].

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

   --------------------------------
   -- Procedures of this package --
   --------------------------------

   procedure Init;
   --  Read the environment variable GNAT2WHY_Args and set the corresponding
   --  options.

end Gnat2Why.Opt;
