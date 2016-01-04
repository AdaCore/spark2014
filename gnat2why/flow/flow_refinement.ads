------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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

--  This package provides the infrastructure to deal with refinement
--  issues: when to use the abstract view or refined view of a subprogram,
--  and if the latter which of the possible refined views.

with Atree;             use Atree;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Sinfo;             use Sinfo;
with Types;             use Types;

package Flow_Refinement is

   ----------------
   -- Flow_Scope --
   ----------------

   --  The scopes we care about in flow analysis are restricted to packages,
   --  protected objects and task objects.
   --
   --  There are eight places any particular variable or subprogram can be
   --  declared or implemented in a:
   --    * package's spec
   --    * package's private part
   --    * package's body
   --    * protected object's spec
   --    * protected object's private part
   --    * protected object's body
   --    * task object's spec
   --    * task object's body
   --
   --  Therefore flow scope is an entity + spec|priv|body.

   type Section_T is (Null_Part, Spec_Part, Private_Part, Body_Part);

   subtype Valid_Section_T is Section_T range Spec_Part .. Body_Part;

   subtype Scope_Id is Entity_Id
   with Dynamic_Predicate => No (Scope_Id) or else
     (Nkind (Scope_Id) in N_Entity and then
      Ekind (Scope_Id) in E_Generic_Package |
                          E_Package         |
                          Protected_Kind    |
                          Task_Kind);

   type Flow_Scope is record
      Ent     : Scope_Id;
      Section : Section_T;
   end record
   with Dynamic_Predicate => (if Present (Flow_Scope.Ent)
                              then Flow_Scope.Section /= Null_Part
                              else Flow_Scope.Section = Null_Part);

   Null_Flow_Scope : constant Flow_Scope := (Empty, Null_Part);

   -----------------
   -- Other types --
   -----------------

   type Contract_T is (Global_Contract, Depends_Contract);

   ---------------
   -- Functions --
   ---------------

   function Present (S : Flow_Scope) return Boolean is (Present (S.Ent));
   --  Returns True iff S is not the Null_Flow_Scope.

   function Private_Scope (S : Flow_Scope) return Flow_Scope
   is (Flow_Scope'(S.Ent, Private_Part))
   with Pre => Present (S);
   --  Returns the private scope for a valid scope.

   function Body_Scope (S : Flow_Scope) return Flow_Scope
   is (Flow_Scope'(S.Ent, Body_Part))
   with Pre => Present (S);
   --  Returns the body scope for a valid scope.

   function Get_Body_Or_Stub (N : Node_Id) return Node_Id;
   --  If a corresponding stub exists, then we return that instead of N.

   ---------------------------
   -- Queries and utilities --
   ---------------------------

   function Is_Visible (N : Node_Id;
                        S : Flow_Scope)
                        return Boolean;
   --  Returns True iff the node N is visible from the scope S.

   function Is_Visible (Target_Scope : Flow_Scope;
                        S            : Flow_Scope)
                        return Boolean;
   --  Returns True if Target_Scope is visible from the scope S.

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope
   with Pre => Present (N);
   --  Given (almost) any node in the AST, work out which flow scope we are in.
   --  If the scope is Standard, return Null_Flow_Scope instead.

   function Subprogram_Refinement_Is_Visible (E : Entity_Id;
                                              S : Flow_Scope)
                                              return Boolean
   with Pre => Ekind (E) in Subprogram_Kind | E_Entry | E_Task_Type;
   --  Return True iff the implementation (and thus refined global or depends)
   --  of subprogram E is visible from S.

   function State_Refinement_Is_Visible (E : Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   with Pre => Ekind (E) = E_Abstract_State;
   --  Return true iff the constituents of E are visible from S.

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
   with Pre => Ekind (E) in Subprogram_Kind | E_Task_Type | E_Entry;
   --  A helpful wrapper around Refinement_Is_Visible: given a subprogram E
   --  and scope S (from which it is called), return the appropriate node
   --  for the abstract or refined version of the global or depends aspect.
   --  We choose the refined version if it exists and is visible, otherwise
   --  we fall back on the abstract version. If we can't find an abstract
   --  version, we return Empty.

   function Down_Project (Vars : Node_Sets.Set;
                          S    : Flow_Scope)
                          return Node_Sets.Set
   with Pre  => (for all V of Vars => Nkind (V) in N_Entity),
        Post => (for all V of Down_Project'Result => Nkind (V) in N_Entity);
   --  Given a set of variables and a scope, recursively expand all
   --  abstract state where its refinement is visible in S.

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id
   with Post => No (Find_Node_In_Initializes'Result)
                  or else Find_Node_In_Initializes'Result = E
                  or else Find_Node_In_Initializes'Result =
                            Encapsulating_State (E);
   --  Returns the node representing E (or its immediately encapsulating
   --  state) in an initializes aspect or Empty.

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope
   with Pre => S.Section in Spec_Part | Private_Part;
   --  Returns the most nested scope of the parent of S.Ent that is visible
   --  from S. Returns the null scope once we reach the Standard package.
   --
   --  This is really an internal function, but as its useful for debug and
   --  trace it has been made visible.

   function Get_Enclosing_Body_Flow_Scope (S : Flow_Scope) return Flow_Scope
   with Pre => S.Section = Body_Part;
   --  Returns the flow scope of the enclosing package or concurrent object if
   --  it exists and the null scope otherwise.

   function Is_Initialized_At_Elaboration (E : Entity_Id;
                                           S : Flow_Scope)
                                           return Boolean;
   --  Checks if the given entity E is initialized at elaboration, as seen
   --  from scope S. For example if you have a nested package where:
   --
   --     package Outer (Initialized "State")
   --        package Inner (X, not initialized, but part of State)
   --
   --  Then from the scope of Inner, X is not initialized at elaboration,
   --  but from the scope of Outer, it is.

   function Mentions_State_With_Visible_Refinement
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Boolean;
   --  Traverses the tree under N and returns True if it finds a state
   --  abstraction whose refinement is visible from Scope.

   function Refinement_Needed (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Entry | E_Task_Type | Subprogram_Kind;
   --  Returns True if a refinement is needed for the given subprogram, entry
   --  or task E.
   --
   --  If no body is present then we return false since we can't decide
   --  (nor need an answer, since we won't analyze the body).
   --
   --  If a body is present then we need a refinement if either:
   --     * no global or depends present
   --     * no refined global, but global mentions state with visible
   --       refinement
   --     * ditto for depends and refined depends

   function Nested_Inside_Concurrent_Object
     (CO : Entity_Id;
      S  : Flow_Scope)
      return Boolean
   with Pre => Present (CO);
   --  Returns True iff S is nested inside concurrent object CO.

end Flow_Refinement;
