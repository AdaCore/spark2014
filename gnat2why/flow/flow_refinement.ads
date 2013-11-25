------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                S p e c                                   --
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

--  This package provides the infrastructure to deal with refinement
--  issues: when to use the abstract view or refined view of a subprogram,
--  and if the latter which of the possible refined views.

with Ada.Containers;

with Atree;          use Atree;
with Einfo;          use Einfo;
with Sinfo;          use Sinfo;
with Types;          use Types;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

use type Ada.Containers.Count_Type;

package Flow_Refinement is

   ----------------
   -- Flow_Scope --
   ----------------

   --  The scope we care about in flow analysis is restrictured to
   --  packages, since we only care about refinement of abstracts state and
   --  packages are the only entities which contain abstract state.
   --
   --  There are three places any particular variable or subprogram can be
   --  declared or implemented: a package's spec, its private part, or its
   --  body. Thus a flow scope is a package entity + spec|priv|body.

   type Section_T is (Null_Part, Spec_Part, Private_Part, Body_Part);

   subtype Valid_Section_T is Section_T range Spec_Part .. Body_Part;

   subtype Package_Id is Entity_Id
     with Dynamic_Predicate => No (Package_Id) or else
       (Nkind (Package_Id) in N_Entity and then
        Ekind (Package_Id) = E_Package);

   type Flow_Scope is record
      Pkg     : Package_Id;
      Section : Section_T;
   end record
     with Dynamic_Predicate => (if Present (Flow_Scope.Pkg)
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

   function Present (S : Flow_Scope) return Boolean is (Present (S.Pkg));
   --  Returns true iff S is not the Null_Flow_Scope.

   function Private_Scope (S : Flow_Scope) return Flow_Scope
   is (Flow_Scope'(S.Pkg, Private_Part))
   with Pre => Present (S);
   --  Returns the private scope for a valid scope.

   ---------------------------
   -- Queries and utilities --
   ---------------------------

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope
     with Pre => Present (N);
   --  Given (almost) any node in the AST, work out which flow scope we're
   --  in. If the scope is Standard, we return Null_Flow_Scope instead.

   function Subprogram_Refinement_Is_Visible (E : Entity_Id;
                                              S : Flow_Scope)
                                              return Boolean
     with Pre => Ekind (E) in Subprogram_Kind;
   --  Return true iff the implementation (and thus refined global or
   --  depends) of subprogram E is visible from S.

   function State_Refinement_Is_Visible (E : Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
     with Pre => Ekind (E) = E_Abstract_State;
   --  Return true iff the constituents of E are visible from S.

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
     with Pre => Ekind (E) in Subprogram_Kind;
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
          Post => (for all V of Down_Project'Result => Nkind (V) in N_Entity)
                  and (Down_Project'Result.Length >= Vars.Length);
   --  Given a set of variables and a scope, recursively expand all
   --  abstract state where its refinement is visible in S. This function
   --  only ever expands the set, it never contracts it.

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope
     with Pre => S.Section in Spec_Part | Private_Part;
   --  Returns the most nested scope of the parent of S.Pkg that is visible
   --  from S. Returns the null scope once we reach the Standard package.
   --
   --  This is really an internal function, but as its useful for debug and
   --  trace it has been made visible.

end Flow_Refinement;
