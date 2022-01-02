------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--            F L O W . A N A L Y S I S . A S S U M P T I O N S             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2021-2022, Altran UK Limited                --
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
------------------------------------------------------------------------------

--  This package deals with the registering of pragma Assume statements for the
--  summary report.

with GNATCOLL.JSON; use GNATCOLL.JSON;
with Snames;        use Snames;
with SPARK_Util;    use SPARK_Util;

package Flow.Analysis.Assumptions is

   function Get_Pragma_Assume_JSON return JSON_Array;
   --  Return all the information registered for all pragma Assume statements

   procedure Register_Pragma_Assume_Statement (Prag : N_Pragma_Id)
     with Pre => Is_Pragma_Check (Prag, Name_Assume);
   --  Registers a pragma Assume statment's filename, line, column, and
   --  subprogram info for the gnatprove summary report.

end Flow.Analysis.Assumptions;
