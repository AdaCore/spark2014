------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

--  This package contains utilities related to the gnat tree.

with Atree; use Atree;
with Einfo; use Einfo;
with Sinfo; use Sinfo;
with Types; use Types;

package Flow_Tree_Utility is

   function Lexicographic_Entity_Order (Left, Right : Entity_Id)
                                        return Boolean;
   --  Ordering for entities based on their unique name. Returns true
   --  if Left is considered to be "less than" Right.

   function Contains_Loop_Entry_Reference (N : Node_Id) return Boolean;
   --  Check for 'Loop_Entry in the given tree.

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id
     with Pre  => Ekind (E) = E_Procedure,
          Post => Nkind (Get_Procedure_Specification'Result) =
            N_Procedure_Specification;

end Flow_Tree_Utility;
