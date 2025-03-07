------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y _ C O U N T E R _ E X A M P L E S           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2016-2025, AdaCore                     --
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

with Types;         use Types;
with VC_Kinds;      use VC_Kinds;

package CE_Display is

   function Create_Pretty_Cntexmp
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr;
      VC_Node : Node_Id;
      VC_K    : VC_Kind)
      return Cntexample_File_Maps.Map;
   --  Create pretty printed counterexample.
   --  Note that deep copy of Cntexmp is made and thus the content of
   --  Cntexmp is not impacted by pretty printing.
   --  @param Cntexmp the counterexample that is pretty printed
   --  @param VC_Loc the location of the construct that triggers VC
   --  @param VC_Node the node associated to the VC
   --  @param VC_K check kind associated to the VC
   --  @return pretty printed counterexample.

   function Get_Cntexmp_One_Liner
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr)
      return String;
   --  Get the part of the counterexample corresponding to the location of
   --  the construct that triggers VC.

   function Get_Environment_CE
     (N    : Node_Id;
      K    : VC_Kind;
      Subp : Node_Id)
      return Cntexample_File_Maps.Map;
   --  Get the elements of the evaluation environment used in the construct
   --  that triggers a VC, with N the AST node corresponding to that construct
   --  and Subp the enclosing subprogram.

   function Remap_VC_Info
     (Cntexmp : Cntexample_File_Maps.Map;
      VC_Loc  : Source_Ptr)
      return Cntexample_File_Maps.Map;
   --  Map counterexample information related to the current VC to the
   --  location of the check in the Ada file.
   --  In Cntexmp, this information is mapped to the field "vc_line" of the
   --  JSON object representing the file where the construct is located.

end CE_Display;
