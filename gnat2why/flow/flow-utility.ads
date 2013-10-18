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
with Sinfo;          use Sinfo;

use type Ada.Containers.Count_Type;

package Flow.Utility is

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Refined_View           : Boolean;
                          Consider_Discriminants : Boolean := False;
                          Globals_For_Proof      : Boolean := False)
   with Pre  => Ekind (Subprogram) in E_Procedure | E_Function,
        Post => (for all G of Reads  => G.Variant = In_View) and
                (for all G of Writes => G.Variant = Out_View);
   --  Given a subprogram call, work out globals from the provided
   --  aspect or the computed globals. The sets returned will contain
   --  Flow_Id with the variant set to Global_In_View and
   --  Global_Out_View.
   --
   --  If refined_view is false, then the global are returned. If
   --  true, the refined globals are returned instead.
   --
   --  If Consider_Discriminants is provided then an out global will
   --  include a corresponding read if the global includes at least
   --  one discriminant.
   --
   --  If Globals_For_Proof is set then the calls to Get_Reads will
   --  not specify Include_Constants.

   function Get_Variable_Set (Scope   : Scope_Ptr;
                              N       : Node_Id;
                              Reduced : Boolean := False)
                              return Flow_Id_Sets.Set;
   --  Obtain all variables used in an expression. If reduced is true,
   --  onbtain only entire variables.

   function Get_Variable_Set (Scope   : Scope_Ptr;
                              L       : List_Id;
                              Reduced : Boolean := False)
                              return Flow_Id_Sets.Set;
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
     (Scope        : Scope_Ptr;
      N            : Node_Id;
      Vars_Defined : out Flow_Id_Sets.Set;
      Vars_Used    : out Flow_Id_Sets.Set)
     with Pre => Nkind (N) in N_Identifier |
                              N_Expanded_Name |
                              N_Selected_Component |
                              N_Indexed_Component |
                              N_Slice |
                              N_Unchecked_Type_Conversion |
                              N_Type_Conversion;
   --  Given the target of an assignment (perhaps the left-hand-side
   --  of an assignment statement or an out vertex in a procedure
   --  call), work out which variables are actually set and which
   --  variables are used to determine what is set (in the case of
   --  arrays).

   function Get_Precondition_Expressions
     (E : Entity_Id) return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Given the entity for a subprogram, return the expression(s) for
   --  its precondition and the condition(s) of its Contract_Cases (or
   --  return the empty list if none of these exist).

   function Get_Postcondition_Expressions
     (E : Entity_Id) return Node_Lists.List
     with Pre => Ekind (E) in Subprogram_Kind | E_Package;
   --  Given the entity for a subprogram or package, return all
   --  expression(s) associated with postconditions: the
   --  postcondition, the rhs for contract cases and the initial
   --  condition; or an empty list of none of these exist.

   function Is_Precondition_Check (N : Node_Id) return Boolean
     with Pre => Nkind (N) = N_Pragma and then
                 Get_Pragma_Id (N) = Pragma_Check;
   --  Given a check pragma, return if this is a precondition check.

   function Is_Discriminant (F : Flow_Id) return Boolean;
   --  Returns true if the given flow id is a record field
   --  representing a discriminant.

   function Contains_Discriminants (F : Flow_Id) return Boolean
     is (for some X of Flatten_Variable (F) => Is_Discriminant (X))
     with Pre => F.Kind in Direct_Mapping | Magic_String;
   --  Returns true if the flattened variable for F contains at least
   --  one discriminant.

end Flow.Utility;
