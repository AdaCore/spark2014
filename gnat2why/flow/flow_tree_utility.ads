------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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

with Atree;  use Atree;
with Einfo;  use Einfo;
with Sinfo;  use Sinfo;
with Snames; use Snames;
with Types;  use Types;

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

   function Might_Be_Main (E : Entity_Id) return Boolean
      with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if E is a library level subprogram without formal
   --  parameters (E is allowed to have global parameters).

   function Is_Package_State (E : Entity_Id) return Boolean;
   --  Returns true if E is declared in a package spec or body. Also
   --  returns true for any abstract state.

   function Get_Body (E : Entity_Id) return Entity_Id
      with Pre  => Ekind (E) in E_Function | E_Procedure,
           Post => (not Present (Get_Body'Result))
                      or else Ekind (Get_Body'Result) = E_Subprogram_Body;
   --  Fetches the body entity for a subprogram with a spec and a body.

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean
      with Pre => Ekind (E) in Subprogram_Kind;
   --  Returns True if the last statement in the Handled_Sequence_Of_Statements
   --  of subprogram E is an N_Raise_Statement.

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
      with Post => Nkind (Get_Enclosing'Result) = K;
   --  Returns the first parent P of N where Nkind (P) = K.

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
     with Pre => (Treat_As_Volatile (E) or Treat_As_Volatile (Etype (E))) and
                 A in Pragma_Async_Readers    | Pragma_Async_Writers |
                      Pragma_Effective_Writes | Pragma_Effective_Reads;
   --  Checks if the given entity (or its type) has the specified aspect.

end Flow_Tree_Utility;
