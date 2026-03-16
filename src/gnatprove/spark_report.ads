------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          S P A R K _ R E P O R T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with GPR2.Project.Tree;
use GPR2;

package Spark_Report is

   procedure Generate_Report
     (Tree       : GPR2.Project.Tree.Object;
      Out_Dir    : String;
      Has_Errors : Boolean;
      Status     : out Integer);
   --  Generate the SPARK analysis report. Out_Dir is where gnatprove.out and
   --  gnatprove.sarif are written. Has_Errors indicates whether earlier phases
   --  of gnatprove produced errors. Status is set to 0 for success, or to a
   --  non-zero error code otherwise.

end Spark_Report;
