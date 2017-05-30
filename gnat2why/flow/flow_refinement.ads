------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                S p e c                                   --
--                                                                          --
--                  Copyright (C) 2013-2017, Altran UK Limited              --
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

--  This package provides the infrastructure to deal with refinement issues:
--  when to use the abstract or refined views of a subprogram, and if the
--  refined view then which one.

with Atree;             use Atree;
with Einfo;             use Einfo;
with Sem_Util;          use Sem_Util;
with Snames;            use Snames;
with Sinfo;             use Sinfo;
with Types;             use Types;

with Checked_Types;     use Checked_Types;
with Common_Containers; use Common_Containers;
with SPARK_Definition;  use SPARK_Definition;
with SPARK_Util.Types;  use SPARK_Util.Types;

package Flow_Refinement is

   ----------------
   -- Flow_Scope --
   ----------------

   --  The scopes we care about in flow analysis are restricted to packages,
   --  protected objects and task objects.
   --
   --  Variables or subprograms can be declared or defined in:
   --    * package's visible part
   --    * package's private part
   --    * package's body
   --    * protected object's visible
   --    * protected object's private part
   --    * protected object's body
   --    * task object's visible
   --    * task object's body
   --
   --  Therefore flow scope is an entity + visible|private|body

   type Any_Declarative_Part is
     (Null_Part, Visible_Part, Private_Part, Body_Part);
   pragma Ordered (Any_Declarative_Part);

   subtype Declarative_Part is Any_Declarative_Part range
     Visible_Part .. Body_Part;

   subtype Scope_Id is Entity_Id
   with Dynamic_Predicate =>
     (if Present (Scope_Id)
      then Ekind (Scope_Id) in E_Package        |
                               E_Protected_Type |
                               E_Task_Type);
   --  Type that defines a subset of legal entities for the use in Flow_Scope

   type Flow_Scope is record
      Ent  : Scope_Id;
      Part : Any_Declarative_Part;
   end record
   with Dynamic_Predicate => (Flow_Scope.Ent = Empty) =
                             (Flow_Scope.Part = Null_Part);
   --  Note: conceptually this is a discrimated record type, but discriminating
   --  on Scope_Id (which is an Entity_Id with a predicate) is troublesome.

   Null_Flow_Scope : constant Flow_Scope := (Empty, Null_Part);

   -----------------
   -- Other types --
   -----------------

   type Contract_T is (Global_Contract, Depends_Contract);

   ---------------
   -- Functions --
   ---------------

   function Present (S : Flow_Scope) return Boolean is (Present (S.Ent));
   --  Returns True iff S is not the Null_Flow_Scope

   function No (S : Flow_Scope) return Boolean is (No (S.Ent));
   --  Returns True iff S is Null_Flow_Scope

   function Private_Scope (S : Flow_Scope) return Flow_Scope
   is (S'Update (Part => Private_Part))
   with Pre => Present (S);
   --  Returns the private scope for a valid scope

   function Body_Scope (S : Flow_Scope) return Flow_Scope
   is (S'Update (Part => Body_Part))
   with Pre => Present (S);
   --  Returns the body scope for a valid scope

   ---------------------------
   -- Queries and utilities --
   ---------------------------

   function Is_Globally_Visible (N : Node_Id) return Boolean;
   --  Returns True iff the node N is visible from outside its compilation unit

   function Is_Visible (N : Node_Id;
                        S : Flow_Scope)
                        return Boolean;
   --  Returns True iff the node N is visible from the scope S

   function Is_Visible (Target_Scope : Flow_Scope;
                        Looking_From : Flow_Scope)
                        return Boolean;
   --  Returns True iff Target_Scope is visible from the scope S

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope
   with Pre => Nkind (N) not in N_Subunit | N_Body_Stub;
   --  Given (almost) any node in the AST, work out which flow scope we are in.
   --  If the scope is Standard, return Null_Flow_Scope instead. For stubs use
   --  the node of the corresponding proper body.

   function Subprogram_Refinement_Is_Visible (E : Entity_Id;
                                              S : Flow_Scope)
                                              return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  Return True iff the implementation (and thus refined global or depends)
   --  of subprogram E is visible from S.

   function State_Refinement_Is_Visible (E : Checked_Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   with Pre => Ekind (E) = E_Abstract_State;
   --  Return true iff the constituents of E are visible from S

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type;
   --  A wrapper around Refinement_Is_Visible: given a subprogram E and scope
   --  S (from which it is called) return the appropriate node for the abstract
   --  or refined version of the global or depends contract. We choose the
   --  refined version if it exists and is visible, otherwise we fall back on
   --  the abstract version. If we can't find an abstract version, we return
   --  Empty.

   function Down_Project (Var : Entity_Id;
                          S   : Flow_Scope)
                          return Node_Sets.Set
   with Post => (for all V of Down_Project'Result =>
                    V in Checked_Entity_Id_Or_Empty);
   --  Given a variable Var and a scope S, recursively expand abstract states
   --  whose refinement is visible in S.

   function Down_Project (Vars : Node_Sets.Set;
                          S    : Flow_Scope)
                          return Node_Sets.Set
   with Pre  => (for all V of Vars => V in Checked_Entity_Id_Or_Empty),
        Post => (for all V of Down_Project'Result =>
                    V in Checked_Entity_Id_Or_Empty);
   --  Same as above, but for many nodes

   function Find_In_Initializes (E : Checked_Entity_Id)
                                 return Entity_Id
   with Post => (if Present (Find_In_Initializes'Result)
                 then Find_In_Initializes'Result in E
                                                  | Encapsulating_State (E));
   --  Returns the node representing E (or its immediately encapsulating state)
   --  in an Initializes aspect or Empty.

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope
   with Pre => S.Part in Visible_Part | Private_Part;
   --  Returns the most nested scope of the parent of S.Ent that is visible
   --  from S. Returns the null scope once we reach the Standard package.
   --
   --  This is really an internal function, but as its useful for debug and
   --  trace it has been made visible.
   --  ??? this should be moved to Functions and renamed to Enclosing_Scope
   --  (since Get is meaningless and Flow repeats the type of parameter)

   function Get_Enclosing_Body_Flow_Scope (S : Flow_Scope) return Flow_Scope
   with Pre => S.Part = Body_Part;
   --  Returns the flow scope of the enclosing package or concurrent object if
   --  it exists and the null scope otherwise.
   --  ??? this should be merged into Get_Enclosing_Body_Flow_Scope

   function Is_Initialized_At_Elaboration (E : Checked_Entity_Id;
                                           S : Flow_Scope)
                                           return Boolean
   with Pre => Ekind (E) in Object_Kind
                          | E_Abstract_State
                          | E_Protected_Type
                          | E_Task_Type;
   --  Checks if the given entity E is initialized at elaboration, as seen from
   --  scope S. For example if you have a nested package where:
   --
   --     package Outer (Initialized "State")
   --        package Inner (X, not initialized, but part of State)
   --
   --  Then from the scope of Inner, X is not initialized at elaboration, but
   --  from the scope of Outer, it is.

   function Mentions_State_With_Visible_Refinement
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Boolean
   with Pre => Get_Pragma_Id (N) in Pragma_Depends | Pragma_Global;
   --  Traverses the tree under N and returns True if it finds a state
   --  abstraction whose refinement is visible from Scope.

   function Refinement_Needed (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Entry | E_Function | E_Procedure | E_Task_Type
               and then Entity_Body_In_SPARK (E);
   --  Returns True if a refinement is needed for the given subprogram, entry
   --  or task E. Only meaningful when entity body is present and is in SPARK.
   --
   --  If a body is present then we need a refinement if either:
   --     * no Global and no Depends is present
   --     * Global mentions state with visible refinement but no Refined_Global
   --       is present
   --     * ditto for Depends and Refined_Depends

   function Nested_Within_Concurrent_Type (T : Type_Id;
                                           S : Flow_Scope)
                                           return Boolean
   with Pre => Is_Concurrent_Type (T);
   --  Returns True iff S is nested inside a concurrent type T

   function Is_Boundary_Subprogram_For_Type (Subprogram : Subprogram_Id;
                                             Typ        : Type_Id)
                                             return Boolean
   with Pre => Has_Invariants_In_SPARK (Typ);

end Flow_Refinement;
