------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                B o d y                                   --
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

with Ada.Containers.Vectors;
with Ada.Containers;         use Ada.Containers;

with Elists;                 use Elists;
with Nlists;                 use Nlists;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with Stand;                  use Stand;

with Output;                 use Output;
with Sprint;                 use Sprint;
with Treepr;                 use Treepr;

with Flow_Types;             use Flow_Types;
with Flow_Debug;             use Flow_Debug;
with Flow_Dependency_Maps;   use Flow_Dependency_Maps;
with Flow_Tree_Utility;      use Flow_Tree_Utility;

with Why;

package body Flow_Refinement is

   function Tree_Contains (T : Node_Id;
                           N : Node_Id)
                           return Boolean;
   --  Returns true iff the tree rooted at T contains node N.

   function Tree_Contains (L : List_Id;
                           N : Node_Id)
                           return Boolean;
   --  Returns true iff the list L contains node N.

   function Is_Visible (Target_Scope : Flow_Scope;
                        S            : Flow_Scope)
                        return Boolean;
   --  Returns true iff the target scope is visible from S. We do this by
   --  moving up the scope DAG from S and testing if we have reached the
   --  target scope. If we hit the top (the null scope) without finding it,
   --  we return False.
   --
   --  The scope DAG may look like a twisty maze, but it is actually
   --  reasonably easy to traverse upwards. The only complication is when
   --  we deal with a private part, in which case we need to quickly check
   --  one extra scope (the visible part), but then we continue on as
   --  normal.
   --
   --     S is...     Next node is...
   --     =======     ===============
   --     X|body      X|priv
   --     X|priv      X|spec                (check this first)
   --                 enclosing_scope (S)   (then continue here)
   --     X|spec      enclosing_scope (S)
   --
   --  The enclosing scope of S is computed by Get_Enclosing_Flow_Scope and
   --  may be one of:
   --
   --     1. The first parent (just going up the AST) of S which is a
   --        package declaration (this deals with nested packages)
   --
   --     2. The first Scope (see einfo.ads) which is a package (this deals
   --        with public and private children)
   --
   --     3. null (if we have hit Standard)
   --
   --  The visibility is the same as before, i.e.
   --     s.section = enclosing_scope(s).section
   --  Unless S is a private descendant, in which case it is always "priv".

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id
     with Post =>
       not Present (Find_Node_In_Initializes'Result)
         or else Find_Node_In_Initializes'Result = E
         or else Find_Node_In_Initializes'Result =
                   Encapsulating_State (E);
   --  Returns the node representing E (or its immediately encapsulating
   --  state) in an initializes aspect or Empty.

   function Get_Body_Or_Stub (N : Node_Id) return Node_Id;
   --  If a corresponding stub exists, then we return that instead of N.

   -------------------
   -- Tree_Contains --
   -------------------

   function Tree_Contains (T : Node_Id;
                           N : Node_Id)
                           return Boolean
   is
      Found : Boolean := False;

      function Proc (X : Node_Id) return Traverse_Result;

      function Proc (X : Node_Id) return Traverse_Result is
      begin
         if X = N then
            Found := True;
            return Abandon;
         else
            return OK;
         end if;
      end Proc;

      procedure Search_For_Node is new Traverse_Proc (Proc);
   begin
      Search_For_Node (T);
      return Found;
   end Tree_Contains;

   function Tree_Contains (L : List_Id;
                           N : Node_Id)
                           return Boolean
   is
      P : Node_Id;
   begin
      P := First (L);
      while Present (P) loop
         if Tree_Contains (P, N) then
            return True;
         end if;
         P := Next (P);
      end loop;
      return False;
   end Tree_Contains;

   ----------------
   -- Is_Visible --
   ----------------

   function Is_Visible (Target_Scope : Flow_Scope;
                        S            : Flow_Scope)
                        return Boolean
   is
      Ptr : Flow_Scope;
   begin
      --  Go upwards from S (the scope we are in) and see if we end up in
      --  Target_Scope (what we're checking if we can see).
      Ptr := S;
      while Ptr /= Null_Flow_Scope loop
         if Ptr = Target_Scope then
            return True;
         end if;

         case Valid_Section_T'(Ptr.Section) is
            when Body_Part =>
               if Flow_Scope'(Ptr.Pkg, Private_Part) = Target_Scope
                 or else Flow_Scope'(Ptr.Pkg, Spec_Part) = Target_Scope
               then
                  return True;
               end if;

               if Get_Enclosing_Body_Flow_Scope (Ptr) /= Null_Flow_Scope then
                  Ptr := Get_Enclosing_Body_Flow_Scope (Ptr);
               else
                  Ptr.Section := Private_Part;
               end if;

            when Private_Part =>
               if Flow_Scope'(Ptr.Pkg, Spec_Part) = Target_Scope then
                  return True;
               end if;
               Ptr := Get_Enclosing_Flow_Scope (Ptr);

            when Spec_Part =>
               Ptr := Get_Enclosing_Flow_Scope (Ptr);
         end case;
      end loop;

      --  Check if Target_Scope is generally visible from anywhere (we
      --  know this if we reach the null flow scope) or if are dealing
      --  with a nested package where we happen to have visibility of
      --  its spec (we know this if we find a scope that is visible
      --  from origin scope while going up the spec parts of the
      --  target scope).
      Ptr := Target_Scope;
      while Ptr /= Null_Flow_Scope and Ptr /= S loop
         case Valid_Section_T'(Ptr.Section) is
            when Spec_Part =>
               Ptr := Get_Enclosing_Flow_Scope (Ptr);
               if Ptr.Section = Private_Part then
                  --  This deals with visibility of private children. A
                  --  package body can see a private child's spec (and test
                  --  for this if the enclosing flow scope of the private
                  --  child's (the parents private part) can be seen from
                  --  S).
                  return Is_Visible (Ptr, S);
               end if;

            when Private_Part | Body_Part =>
               exit;
         end case;
      end loop;
      return Ptr = Null_Flow_Scope
        or else Ptr = S
        or else (Ptr /= Target_Scope
                   and then Is_Visible (Ptr, S));
   end Is_Visible;

   function Is_Visible (N : Node_Id;
                        S : Flow_Scope)
                        return Boolean
   is
      Target_Scope : constant Flow_Scope := Get_Flow_Scope (N);
   begin
      return Is_Visible (Target_Scope, S);
   end Is_Visible;

   ------------------------------
   -- Get_Enclosing_Flow_Scope --
   ------------------------------

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope
   is
      Enclosing_Scope : Flow_Scope := S;
      Ptr             : Node_Id    := S.Pkg;
   begin
      while Nkind (Ptr) /= N_Package_Declaration loop
         Ptr := Parent (Ptr);
      end loop;
      Enclosing_Scope := Get_Flow_Scope (Ptr);

      if Enclosing_Scope = Null_Flow_Scope and then
        Scope (S.Pkg) /= Standard_Standard
      then
         Ptr := Scope (S.Pkg);
         while Present (Ptr) and then Ekind (Ptr) /= E_Package loop
            Ptr := Scope (Ptr);
         end loop;
         if Present (Ptr) and then Ptr /= Standard_Standard then
            Enclosing_Scope := Flow_Scope'(Ptr, S.Section);
         end if;
      end if;

      if Is_Private_Descendant (S.Pkg) then
         Enclosing_Scope.Section := Private_Part;
      end if;

      return Enclosing_Scope;
   end Get_Enclosing_Flow_Scope;

   -----------------------------------
   -- Get_Enclosing_Body_Flow_Scope --
   -----------------------------------

   function Get_Enclosing_Body_Flow_Scope (S : Flow_Scope) return Flow_Scope is
      P : Node_Id;
   begin
      P := Body_Entity (S.Pkg);

      --  We need to get to the node that is above the N_Package_Body
      --  that corresponds to flow scope S.
      while Nkind (P) /= N_Package_Body loop
         P := Parent (P);
      end loop;
      P := Parent (P);

      return Get_Flow_Scope (P);
   end Get_Enclosing_Body_Flow_Scope;

   --------------------
   -- Get_Flow_Scope --
   --------------------

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope is
      P : Node_Id    := N;
      V : Section_T;
   begin
      while Present (P) loop
         P := Get_Body_Or_Stub (P);
         case Nkind (P) is
            when N_Package_Body =>
               V := Body_Part;
               P := Defining_Unit_Name (P);
               if Nkind (P) = N_Defining_Program_Unit_Name then
                  P := Defining_Identifier (P);
               end if;
               P := Spec_Entity (P);
               exit;

            when N_Package_Specification =>
               if Tree_Contains (Private_Declarations (P),
                                 Get_Body_Or_Stub (N))
               then
                  V := Private_Part;
               else
                  V := Spec_Part;
               end if;
               P := Defining_Unit_Name (P);
               if Nkind (P) = N_Defining_Program_Unit_Name then
                  P := Defining_Identifier (P);
               end if;
               exit;

            when N_Aspect_Specification =>
               --  We only get here when we call Get_Flow_Scope on an
               --  abstract state. On this occasion we want to return
               --  the Spec_Part followed by the name of the package
               --  that introduces the abstract state.
               pragma Assert (Nkind (N) = N_Defining_Identifier
                                and then Ekind (N) = E_Abstract_State);

               if Nkind (Parent (P)) = N_Package_Declaration then
                  V := Spec_Part;

                  P := Defining_Unit_Name (Specification (Parent (P)));
                  if Nkind (P) = N_Defining_Program_Unit_Name then
                     P := Defining_Identifier (P);
                  end if;
                  exit;
               end if;

            when others =>
               null;
         end case;

         P := Parent (P);
      end loop;

      if Present (P) then
         return (Pkg     => P,
                 Section => V);
      else
         return Null_Flow_Scope;
      end if;
   end Get_Flow_Scope;

   --------------------------------------
   -- Subprogram_Refinement_Is_Visible --
   --------------------------------------

   function Subprogram_Refinement_Is_Visible (E : Entity_Id;
                                              S : Flow_Scope)
                                              return Boolean
   is
      Body_E : constant Entity_Id := Get_Body (E);
   begin
      if not Present (S) then
         --  From the standard scope we won't be able to see much...
         return False;
      end if;

      if No (Body_E) then
         --  If we don't even have it in the AST, then its a safe bet that
         --  we can't see the refinement...
         return False;
      end if;
      pragma Assert_And_Cut (Present (Body_E));

      return Is_Visible (Get_Body_Or_Stub (Body_E), S);
   end Subprogram_Refinement_Is_Visible;

   ---------------------------------
   -- State_Refinement_Is_Visible --
   ---------------------------------

   function State_Refinement_Is_Visible (E : Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   is
      Ref_Scope : Flow_Scope;
   begin
      Ref_Scope := Get_Flow_Scope (E);
      pragma Assert (Present (Ref_Scope));
      Ref_Scope.Section := Body_Part;

      return Is_Visible (Ref_Scope, S);
   end State_Refinement_Is_Visible;

   -----------------------
   -- Get_Contract_Node --
   -----------------------

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
   is
      Body_E : Node_Id;
      N      : Node_Id := Empty;
   begin
      if Subprogram_Refinement_Is_Visible (E, S) then
         Body_E := Get_Body (E);
         pragma Assert (Present (Body_E));

         N := Get_Pragma
           (Get_Body_Or_Stub (Body_E),
            (case C is
               when Global_Contract  => Pragma_Refined_Global,
               when Depends_Contract => Pragma_Refined_Depends));
      end if;

      if No (N) then
         N := Get_Pragma
           (E,
            (case C is
               when Global_Contract  => Pragma_Global,
               when Depends_Contract => Pragma_Depends));
      end if;

      return N;
   end Get_Contract_Node;

   ------------------
   -- Down_Project --
   ------------------

   function Down_Project (Vars : Node_Sets.Set;
                          S    : Flow_Scope)
                          return Node_Sets.Set
   is
      function Expand (E : Entity_Id) return Node_Sets.Set;
      --  We return either E if its refinement is not visible, or all
      --  consitituents of E otherwise.
      --
      --  If E is not abstract state, we also just return E.

      ------------
      -- Expand --
      ------------

      function Expand (E : Entity_Id) return Node_Sets.Set
      is
         Tmp : Node_Sets.Set := Node_Sets.Empty_Set;
         Ptr : Elmt_Id;
         Hs  : Boolean := False;
      begin
         case Ekind (E) is
            when E_Abstract_State =>
               if State_Refinement_Is_Visible (E, S) then
                  Ptr := First_Elmt (Refinement_Constituents (E));
                  while Present (Ptr) loop
                     if Nkind (Node (Ptr)) /= N_Null then
                        Tmp.Union (Expand (Node (Ptr)));
                     end if;
                     Ptr := Next_Elmt (Ptr);
                  end loop;
               else
                  Hs := True;
               end if;

               Ptr := First_Elmt (Part_Of_Constituents (E));
               while Present (Ptr) loop
                  if Is_Visible (Node (Ptr), S) then
                     Tmp.Union (Expand (Node (Ptr)));
                  else
                     Hs := True;
                  end if;
                  Ptr := Next_Elmt (Ptr);
               end loop;

               if Hs then
                  --  We seem to have an abstract state which has no
                  --  refinement, or where we have unexpanded state. Lets
                  --  include the abstract state itself.
                  Tmp.Include (E);
               end if;

            when others =>
               Tmp.Include (E);
         end case;
         return Tmp;
      end Expand;

      P : Node_Sets.Set := Node_Sets.Empty_Set;
   begin
      for V of Vars loop
         P.Union (Expand (V));
      end loop;
      return P;
   end Down_Project;

   ------------------------------
   -- Find_Node_In_Initializes --
   ------------------------------

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id is
      P          : Entity_Id          := E;
      Init       : Node_Id;
      M          : Dependency_Maps.Map;
      F          : Flow_Id;
      N          : Node_Id;

      Target_Ent : constant Entity_Id :=
        (if Present (Encapsulating_State (E)) and
            Scope (E) = Scope (Encapsulating_State (E))
         then Encapsulating_State (E)
         else Unique_Entity (E));
      --  What we are searching for. Either the entity itself, or, if this
      --  entity is part of abstract state of its immediately enclosing
      --  package, that abstract state.

   begin
      while Ekind (P) /= E_Package loop
         case Ekind (P) is
            when E_Package_Body =>
               raise Why.Not_Implemented;
            when others =>
               P := Scope (P);
         end case;
      end loop;
      Init := Get_Pragma (P, Pragma_Initializes);

      M := Parse_Initializes (Init, P);
      for Initialized_Var in M.Iterate loop
         F := Dependency_Maps.Key (Initialized_Var);
         N := (if F.Kind in Direct_Mapping | Record_Field
               then Get_Direct_Mapping_Id (F)
               else Empty);

         if N = Target_Ent then
            return N;
         end if;
      end loop;

      return Empty;
   end Find_Node_In_Initializes;

   ----------------------
   -- Get_Body_Or_Stub --
   ----------------------

   function Get_Body_Or_Stub (N : Node_Id) return Node_Id is
   begin
      if Nkind (Parent (N)) = N_Subunit
        and then Present (Corresponding_Stub (Parent (N)))
      then
         return Corresponding_Stub (Parent (N));
      else
         return N;
      end if;
   end Get_Body_Or_Stub;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (E : Entity_Id;
                                           S : Flow_Scope)
                                           return Boolean
   is
      Trace : constant Boolean := False;
      --  Enable this for some tracing output.

      package Scope_Vectors is new Ada.Containers.Vectors
        (Index_Type   => Positive,
         Element_Type => Flow_Scope);

      function Ancestor (S : Flow_Scope) return Flow_Scope
        with Pre => Present (S);
      --  Determine the immediate ancestor of S.

      function Heritage (S : Flow_Scope) return Scope_Vectors.Vector
        with Post => not Heritage'Result.Is_Empty and then
                     Heritage'Result.First_Element = Null_Flow_Scope and then
                     Heritage'Result.Last_Element = S;
      --  Determine all ancestors of S up to and including Standard.

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope;
      --  Return the common ancestor of both flow scopes.

      --------------
      -- Ancestor --
      --------------

      function Ancestor (S : Flow_Scope) return Flow_Scope
      is
      begin
         case Valid_Section_T'(S.Section) is
            when Body_Part =>
               return S'Update (Section => Private_Part);

            when Private_Part | Spec_Part =>
               return Get_Enclosing_Flow_Scope (S);
         end case;
      end Ancestor;

      --------------
      -- Heritage --
      --------------

      function Heritage (S : Flow_Scope) return Scope_Vectors.Vector is
         Ptr : Flow_Scope := S;
         V   : Scope_Vectors.Vector := Scope_Vectors.Empty_Vector;
      begin
         V.Append (Ptr);
         while Present (Ptr) loop
            Ptr := Ancestor (Ptr);
            V.Append (Ptr);
         end loop;
         V.Reverse_Elements;
         return V;
      end Heritage;

      ---------------------
      -- Common_Ancestor --
      ---------------------

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope
      is
         L1  : constant Scope_Vectors.Vector := Heritage (A);
         L2  : constant Scope_Vectors.Vector := Heritage (B);

         Ptr : Natural := 0;
      begin
         loop
            if Count_Type (Ptr) = L1.Length or
              Count_Type (Ptr) = L2.Length
            then
               if Ptr >= 1 then
                  return L1 (Ptr);
               else
                  return Null_Flow_Scope;
               end if;
            end if;
            Ptr := Ptr + 1;
            if L1 (Ptr) /= L2 (Ptr) then
               Ptr := Ptr - 1;
               if Ptr >= 1 then
                  return L1 (Ptr);
               else
                  return Null_Flow_Scope;
               end if;
            end if;
            pragma Loop_Variant   (Increases => Ptr);
            pragma Loop_Invariant (L1 (Ptr) = L2 (Ptr));
         end loop;
      end Common_Ancestor;

      Ent  : Entity_Id  := E;
      Ptr  : Flow_Scope := Get_Flow_Scope (E);
      Init : Boolean;

      Common_Scope : constant Flow_Scope := Common_Ancestor (Ptr, S);

   begin

      if Trace then
         Write_Str ("Query: ");
         Sprint_Node (E);
         Write_Str (" from scope ");
         Print_Flow_Scope (S);
         Write_Eol;

         Write_Str ("   -> common scope: ");
         Print_Flow_Scope (Common_Scope);
         Write_Eol;
      end if;

      loop
         if Trace then
            Write_Str ("   -> looking at ");
            Sprint_Node (Ent);
            Write_Eol;
         end if;

         case Ekind (Ent) is
            when E_Abstract_State =>
               null;

            when E_Variable =>
               if not Is_Package_State (Ent) then
                  return False;
               end if;

            when E_Constant =>
               return False;

            when others =>
               Print_Tree_Node (Ent);
               raise Program_Error;
         end case;

         Init := Present (Find_Node_In_Initializes (Ent));

         if Ptr.Pkg = Common_Scope.Pkg or Ptr.Pkg = S.Pkg then
            if Trace then
               Write_Str ("   -> in common scope or home");
               Write_Eol;
            end if;

            if Ekind (Ent) = E_Variable and then
              Present (Encapsulating_State (Ent)) and then
              Get_Flow_Scope (Encapsulating_State (Ent)).Pkg = Ptr.Pkg
            then
               if Trace then
                  Write_Str ("   -> looking up");
                  Write_Eol;
               end if;
               Init := Present (Find_Node_In_Initializes
                                  (Encapsulating_State (Ent)));
            end if;
            return Init;
         end if;

         Ent := Encapsulating_State (Ent);
         if Present (Ent) then
            Ptr := Get_Flow_Scope (Ent);
         else
            return Init;
         end if;
      end loop;

   end Is_Initialized_At_Elaboration;

end Flow_Refinement;
