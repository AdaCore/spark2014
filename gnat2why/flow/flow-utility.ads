------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W . U T I L I T Y                          --
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

--  This package contains a bunch of helpful procedures used
--  throughout flow analysis.

with Ada.Containers;

with Sem_Util;       use Sem_Util;
with Snames;         use Snames;

use type Ada.Containers.Count_Type;

package Flow.Utility is

   function Get_Variable_Set (N : Node_Id) return Flow_Id_Sets.Set;
   --  Obtain all variables used in an expression.

   function Get_Variable_Set (L : List_Id) return Flow_Id_Sets.Set;
   --  As above, but operating on a list.

   function Flatten_Variable (E : Entity_Id) return Flow_Id_Sets.Set;
   --  Returns a set of flow_ids for all parts of the unique entity
   --  for E. For records this includes all subcomponents, for
   --  everything else this is just the variable E.

   function Flatten_Variable (F : Flow_Id) return Flow_Id_Sets.Set
     with Pre => F.Kind in Direct_Mapping | Magic_String;
   --  As above, but for flow ids.

   function Get_Full_Type (E : Entity_Id) return Entity_Id;
   --  Get the type of the given entity. Ignores private types and
   --  always returns the full view.

   procedure Untangle_Assignment_Target
     (N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
   with Pre => Nkind (N) in N_Identifier |
                            N_Expanded_Name |
                            N_Selected_Component |
                            N_Indexed_Component |
                            N_Slice;
   --  Given the target of an assignment (perhaps the left-hand-side
   --  of an assignment statement or an out vertex in a procedure
   --  call), work out which variables are actually set and which
   --  variables are used to determine what is set (in the case of
   --  arrays).

   function Get_Preconditions (E : Entity_Id) return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Given the entity for a subprogram, return the expression(s) for
   --  its precondition (or the empty list).

   function Is_Precondition_Check (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Pragma and then
                 Get_Pragma_Id (N) = Pragma_Check;
   --  Given a check pragma, return if this is a precondition check.

end Flow.Utility;
