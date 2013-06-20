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

   ----------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------

   subtype Scope_Ptr is Node_Id
     with Dynamic_Predicate =>
     Nkind (Scope_Ptr) in N_Function_Specification |
                          N_Procedure_Specification |
                          N_Package_Specification |
                          N_Subprogram_Body |
                          N_Package_Body
     or else Scope_Ptr = Empty;

   ----------------------------------------------------------------------
   --  Functions
   ----------------------------------------------------------------------

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

   function Might_Be_Main (E : Entity_Id) return Boolean
      with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if E is a library level subprogram without formal
   --  parameters (E is allowed to have global parameters).

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id
   with Post => not Present (Find_Node_In_Initializes'Result) or else
                Entity (Find_Node_In_Initializes'Result) = E;
   --  Returns the node representing E in an initializes aspect or Empty.

   function Is_Initialized_At_Elaboration (E : Entity_Id) return Boolean
     is (Present (Find_Node_In_Initializes (E)));
   --  Returns true if E is covered by an initializes aspect.

   function Get_Body (E : Entity_Id) return Entity_Id
     with Pre => Ekind (E) in E_Function | E_Procedure,
          Post => (not Present (Get_Body'Result)) or else
                  Ekind (Get_Body'Result) = E_Subprogram_Body;
   --  Fetches the body entity for a subprogram with a spec and a body.

   function Get_Enclosing_Scope (N : Node_Id) return Scope_Ptr;

   function Should_Use_Refined_View (Scope : Scope_Ptr;
                                     N     : Node_Id)
                                     return Boolean
     with Pre => Nkind (N) in N_Subprogram_Call;
   --  For a given function or procedure call N, this function returns
   --  true if we should use the Refined_Global and Refined_Depends
   --  aspects or the Global and Depends aspects.
   --
   --  !!! This currently always returns true.

end Flow_Tree_Utility;
