------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2013-2015, Altran UK Limited                 --
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

with Ada.Containers;

with Atree;             use Atree;
with Einfo;             use Einfo;
with Sinfo;             use Sinfo;
with Snames;            use Snames;
with Types;             use Types;

package Flow_Tree_Utility with
   Initial_Condition => not Is_Initialized
is

   procedure Initialize;
   --  Set up state required by some functions in this package.

   function Is_Initialized return Boolean;
   --  Tests if we're initialized.

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id
     with Pre  => Ekind (E) = E_Procedure,
          Post => Nkind (Get_Procedure_Specification'Result) =
            N_Procedure_Specification;

   function Might_Be_Main (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if E is a library level subprogram without formal
   --  parameters (E is allowed to have global parameters).

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  Returns True if E is declared in a package spec or body. Also
   --  returns True for any abstract state.

   function Get_Body (E : Entity_Id) return Entity_Id
     with Pre  => Ekind (E) in E_Function | E_Procedure,
          Post => (not Present (Get_Body'Result))
                     or else Ekind (Get_Body'Result) = E_Subprogram_Body;
   --  Fetches the body entity for a subprogram with a spec and a body.

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
     with Post => Nkind (Get_Enclosing'Result) = K;
   --  Returns the first parent P of N where Nkind (P) = K.

   function Has_Volatile (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity;
   --  Checks if the given entity is volatile.

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
     with Pre => Has_Volatile (E) and
                 A in Pragma_Async_Readers    | Pragma_Async_Writers |
                      Pragma_Effective_Writes | Pragma_Effective_Reads;
   --  Checks if the given entity (or its type) has the specified aspect.

   function Is_Tick_Update (N : Node_Id) return Boolean
   is (Nkind (N) = N_Attribute_Reference  and then
         Get_Attribute_Id (Attribute_Name (N)) = Attribute_Update);
   --  Checks if the given node is a 'Update node.

   function Component_Hash (E : Entity_Id) return Ada.Containers.Hash_Type
     with Pre => Is_Initialized and then
                 Nkind (E) in N_Entity and then
                 Ekind (E) in E_Component | E_Discriminant;
   --  Compute a suitable hash for the given record component.

   function Same_Component (C1, C2 : Entity_Id) return Boolean
     with Pre => Is_Initialized and then
                 Nkind (C1) in N_Entity and then
                 Nkind (C2) in N_Entity and then
                 Ekind (C1) in E_Component | E_Discriminant  and then
                 Ekind (C2) in E_Component | E_Discriminant;
   --  Given two record components, checks if one can be considered to be
   --  the `same' component (for purposes of flow analysis). For example a
   --  record might contain component x, and its derived record also
   --  contains this component x (but its a different entity). This
   --  function can be used to check for this equivalence.

   function Has_Extensions_Visible_Aspect (E : Entity_Id) return Boolean
     with Pre => Nkind (E) in N_Entity and then
                 Ekind (E) in Subprogram_Kind;
   --  Checks if extensions are visible for this subprogram.

   function Get_Full_Type_Without_Checking (N : Node_Id) return Entity_Id
     with Pre => Present (N);
   --  Get the type of the given entity. This function looks through
   --  private types and should be used with extreme care.

private
   Init_Done : Boolean := False;

   --------------------
   -- Is_Initialized --
   --------------------

   function Is_Initialized return Boolean is (Init_Done);

end Flow_Tree_Utility;
