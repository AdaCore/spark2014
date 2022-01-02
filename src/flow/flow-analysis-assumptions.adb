------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--            F L O W . A N A L Y S I S . A S S U M P T I O N S             --
--                                                                          --
--                                 B o d y                                  --
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

with Assumption_Types; use Assumption_Types;
with Flow_Refinement;  use Flow_Refinement;
with Sinput;           use Sinput;

package body Flow.Analysis.Assumptions is

   Pragma_Assume_Msgs : JSON_Array;

   ----------------------------
   -- Get_Pragma_Assume_JSON --
   ----------------------------

   function Get_Pragma_Assume_JSON return JSON_Array is (Pragma_Assume_Msgs);

   --------------------------------------
   -- Register_Pragma_Assume_Statement --
   --------------------------------------

   procedure Register_Pragma_Assume_Statement (Prag : N_Pragma_Id) is
      Result : constant JSON_Value := Create_Object;
      Slc    : constant Source_Ptr := Sloc (Prag);
      File   : constant String     := File_Name (Slc);
      Line   : constant Positive   :=
        Positive (Get_Physical_Line_Number (Slc));
      Col    : constant Positive   :=
        Positive (Get_Column_Number (Slc));
   begin
      Set_Field (Result, "file", File);
      Set_Field (Result, "line", Line);
      Set_Field (Result, "col", Col);
      Set_Field (Result, "entity",
                 To_JSON (Entity_To_Subp_Assumption
                   (Get_Flow_Scope (Prag).Ent)));
      Append (Pragma_Assume_Msgs, Result);
   end Register_Pragma_Assume_Statement;

end Flow.Analysis.Assumptions;
