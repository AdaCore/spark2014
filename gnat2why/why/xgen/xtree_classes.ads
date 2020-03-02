------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        X T R E E _ C L A S S E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Outputs;      use Outputs;
with Xkind_Tables; use Xkind_Tables;
with Why.Sinfo;    use Why.Sinfo;

package Xtree_Classes is

   procedure Print_Class_Case_Expression
     (O            : in out Output_Record;
      CI           : Class_Info;
      Param        : Wide_String;
      Default      : Wide_String;
      Process_Kind : not null access procedure
                       (O    : in out Output_Record;
                        Kind : Why_Node_Kind);
      Case_Expr    : Boolean := True);
   --  Generate a case statement or a case expression (depending on Case_Expr)
   --  that dispatch over Param's kind, and call Process_Kind for each kind.

end Xtree_Classes;
