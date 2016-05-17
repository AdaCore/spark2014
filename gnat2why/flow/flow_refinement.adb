------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                B o d y                                   --
--                                                                          --
--               Copyright (C) 2013-2016, Altran UK Limited                 --
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

with Ada.Containers;         use Ada.Containers;
with Ada.Containers.Vectors;

with Nlists;                 use Nlists;
with Output;                 use Output;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with Sprint;                 use Sprint;
with Stand;                  use Stand;
with Treepr;                 use Treepr;

with Common_Iterators;       use Common_Iterators;
with SPARK_Util;             use SPARK_Util;
with Why;

with Flow_Debug;             use Flow_Debug;
with Flow_Dependency_Maps;   use Flow_Dependency_Maps;
with Flow_Types;             use Flow_Types;

package body Flow_Refinement is

   function Tree_Contains (T : Node_Id;
                           N : Node_Id)
                           return Boolean;
   --  Returns True iff the tree rooted at T contains node N.

   function Tree_Contains (L : List_Id;
                           N : Node_Id)
                           return Boolean;
   --  Returns True iff the list L contains node N.

   -------------------
   -- Tree_Contains --
   -------------------

   function Tree_Contains (T : Node_Id;
                           N : Node_Id)
                           return Boolean
   is
      Found : Boolean := False;

      function Proc (X : Node_Id) return Traverse_Result;

      ----------
      -- Proc --
      ----------

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

   --  Start of processing for Tree_Contains

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
      --  Returns True iff the target scope is visible from S. We do this by
      --  moving up the scope DAG from S and testing if we have reached the
      --  target scope. If we hit the top (the null scope) without finding it,
      --  we return False.
      --
      --  The scope DAG may look like a twisty maze, but it is actually
      --  reasonably easy to traverse upwards. The only complication is when we
      --  deal with a private part, in which case we need to quickly check one
      --  extra scope (the visible part), but then we continue on as normal.
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
      --        package/PO declaration (this deals with nested packages)
      --
      --     2. The first Scope (see einfo.ads) which is a package/PO (this
      --        deals with public and private children)
      --
      --     3. null (if we have hit Standard)
      --
      --  The visibility is the same as before, i.e.
      --     s.section = enclosing_scope(s).section
      --  Unless S is a private descendant, in which case it is always "priv".

      Ptr : Flow_Scope;
   begin
      --  Go upwards from S (the scope we are in) and see if we end up in
      --  Target_Scope (what we're checking if we can see).
      Ptr := S;
      while Present (Ptr) loop
         if Ptr = Target_Scope then
            return True;
         end if;

         case Valid_Section_T'(Ptr.Section) is
            when Body_Part =>
               if Flow_Scope'(Ptr.Ent, Private_Part) = Target_Scope
                 or else Flow_Scope'(Ptr.Ent, Spec_Part) = Target_Scope
               then
                  return True;
               end if;

               if Present (Get_Enclosing_Body_Flow_Scope (Ptr)) then
                  Ptr := Get_Enclosing_Body_Flow_Scope (Ptr);
               else
                  Ptr.Section := Private_Part;
               end if;

            when Private_Part =>
               if Flow_Scope'(Ptr.Ent, Spec_Part) = Target_Scope then
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
      while Present (Ptr) and then Ptr /= S loop
         case Valid_Section_T'(Ptr.Section) is
            when Spec_Part =>
               Ptr := Get_Enclosing_Flow_Scope (Ptr);
               if Present (Ptr) and then Ptr.Section = Private_Part then
                  --  This deals with visibility of private children. A package
                  --  body can see a private child's spec (and test for this if
                  --  the enclosing flow scope of the private child's, i.e. the
                  --  parents private part, can be seen from S).
                  return Is_Visible (Ptr, S);
               end if;

            when Private_Part | Body_Part =>
               exit;
         end case;
      end loop;

      return No (Ptr)
        or else Ptr = S
        or else (Ptr /= Target_Scope and then Is_Visible (Ptr, S));

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

   function Get_Enclosing_Flow_Scope (S : Flow_Scope) return Flow_Scope is
      Enclosing_Scope : Flow_Scope := S;
      Ptr             : Node_Id    := S.Ent;
   begin
      while Nkind (Ptr) not in N_Package_Declaration        |
                               N_Protected_Type_Declaration |
                               N_Task_Type_Declaration
      loop
         Ptr := Parent (Ptr);
      end loop;
      Enclosing_Scope := Get_Flow_Scope (Ptr);

      if No (Enclosing_Scope)
        and then Scope (S.Ent) /= Standard_Standard
      then
         Ptr := Scope (S.Ent);
         while Present (Ptr)
           and then Ekind (Ptr) not in E_Package      |
                                       Protected_Kind |
                                       Task_Kind
         loop
            Ptr := Scope (Ptr);
         end loop;
         if Present (Ptr)
           and then Ptr /= Standard_Standard
         then
            Enclosing_Scope := Flow_Scope'(Ptr, S.Section);
         end if;
      end if;

      if Is_Private_Descendant (S.Ent) then
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
      P := S.Ent;
      while Present (P)
        and then Nkind (P) not in N_Generic_Package_Declaration |
                                  N_Package_Declaration         |
                                  N_Protected_Type_Declaration  |
                                  N_Task_Type_Declaration
      loop
         P := Parent (P);
      end loop;

      case Nkind (P) is
         when N_Generic_Package_Declaration |
              N_Package_Declaration         |
              N_Protected_Type_Declaration  |
              N_Task_Type_Declaration       =>
            P := Corresponding_Body (P);

         when others =>
            raise Why.Unexpected_Node;
      end case;

      --  We need to get to the node that is above the
      --  N_Package_Body/N_Protected_Body/N_Task_Body that corresponds to flow
      --  scope S.
      while Nkind (P) not in N_Package_Body   |
                             N_Protected_Body |
                             N_Task_Body
      loop
         P := Parent (P);
      end loop;
      P := Parent (P);

      return Get_Flow_Scope (P);
   end Get_Enclosing_Body_Flow_Scope;

   --------------------
   -- Get_Flow_Scope --
   --------------------

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope is
      P : Node_Id := N;
      V : Valid_Section_T;
   begin
      while Present (P) loop
         P := Get_Body_Or_Stub (P);
         case Nkind (P) is
            when N_Package_Body | N_Protected_Body | N_Task_Body =>
               V := Body_Part;
               case Nkind (P) is
                  when N_Package_Body =>
                     P := Defining_Unit_Name (P);
                     if Nkind (P) = N_Defining_Program_Unit_Name then
                        P := Defining_Identifier (P);
                     end if;
                     P := Spec_Entity (P);

                  when N_Protected_Body | N_Task_Body =>
                     P := Corresponding_Spec (P);

                  when others =>
                     raise Program_Error;
               end case;
               exit;

            when N_Package_Specification |
                 N_Protected_Definition  |
                 N_Task_Definition       =>
               if Nkind (P) = N_Task_Definition
                 or else not Tree_Contains (Private_Declarations (P),
                                            Get_Body_Or_Stub (N))
               then
                  V := Spec_Part;
               else
                  V := Private_Part;
               end if;

               case Nkind (P) is
                  when N_Package_Specification =>
                     P := Defining_Unit_Name (P);
                     if Nkind (P) = N_Defining_Program_Unit_Name then
                        P := Defining_Identifier (P);
                     end if;

                  when N_Protected_Definition | N_Task_Definition  =>
                     P := Defining_Identifier (Parent (P));

                  when others =>
                     raise Program_Error;
               end case;
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

         --  If we get a node from some contract, we will get the node from
         --  the generated pragma instead. This pragma does not have a
         --  parent set, so in this case we jump to the entity the aspect
         --  is for.
         if Nkind (P) = N_Pragma and then From_Aspect_Specification (P) then
            P := Corresponding_Aspect (P);
            pragma Assert (Nkind (P) = N_Aspect_Specification);
            P := Entity (P);
         else
            P := Parent (P);
         end if;
      end loop;

      if Present (P) then
         return (Ent     => P,
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
      Body_E : constant Entity_Id := Get_Body_Entity (E);
   begin
      if No (S) then
         --  From the standard scope we won't be able to see much...
         return False;
      end if;

      if No (Body_E) then
         --  If we don't even have it in the AST, then it's a safe bet that
         --  we can't see the refinement...
         return False;
      end if;

      return Is_Visible (Get_Body_Or_Stub (Body_E), S);
   end Subprogram_Refinement_Is_Visible;

   ---------------------------------
   -- State_Refinement_Is_Visible --
   ---------------------------------

   function State_Refinement_Is_Visible (E : Entity_Id;
                                         S : Flow_Scope)
                                         return Boolean
   is
     (Is_Visible (Body_Scope (Get_Flow_Scope (E)), S));

   -----------------------
   -- Get_Contract_Node --
   -----------------------

   function Get_Contract_Node (E : Entity_Id;
                               S : Flow_Scope;
                               C : Contract_T)
                               return Node_Id
   is
      Body_E : constant Entity_Id := Get_Body_Entity (E);
      N      : Node_Id := Empty;
   begin
      if Subprogram_Refinement_Is_Visible (E, S) then
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

      function Expand (E : Entity_Id) return Node_Sets.Set is
         Tmp                        : Node_Sets.Set := Node_Sets.Empty_Set;
         Possible_Hidden_Components : Boolean       := False;
      begin
         case Ekind (E) is
            when E_Abstract_State =>
               if State_Refinement_Is_Visible (E, S) then
                  for C of Iter (Refinement_Constituents (E)) loop
                     if Nkind (C) /= N_Null then
                        Tmp.Union (Expand (C));
                     end if;
                  end loop;
               else
                  Possible_Hidden_Components := True;
               end if;

               for C of Iter (Part_Of_Constituents (E)) loop
                  if Is_Visible (C, S) then
                     Tmp.Union (Expand (C));
                  else
                     Possible_Hidden_Components := True;
                  end if;
               end loop;

               if Possible_Hidden_Components then
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

   --  Start of processing for Down_Project

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
      P          : Entity_Id := E;
      Init       : Node_Id;
      M          : Dependency_Maps.Map;
      F          : Flow_Id;
      N          : Node_Id;

      Target_Ent : constant Entity_Id :=
        (if Present (Encapsulating_State (E))
           and then Scope (E) = Scope (Encapsulating_State (E))
         then Encapsulating_State (E)
         else Unique_Entity (E));
      --  What we are searching for. Either the entity itself, or, if this
      --  entity is part of abstract state of its immediately enclosing
      --  package, that abstract state.

   begin
      while Ekind (P) not in E_Package | E_Generic_Package loop
         case Ekind (P) is
            when E_Package_Body =>
               raise Why.Not_Implemented;
            when others =>
               P := Scope (P);
         end case;
      end loop;
      Init := Get_Pragma (P, Pragma_Initializes);

      M := Parse_Initializes (Init, P, Get_Flow_Scope (P));

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
                   No (Heritage'Result.First_Element) and then
                   Heritage'Result.Last_Element = S;
      --  Determine all ancestors of S up to and including Standard.

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope;
      --  Return the common ancestor of both flow scopes.

      --------------
      -- Ancestor --
      --------------

      function Ancestor (S : Flow_Scope) return Flow_Scope is
      begin
         case Valid_Section_T'(S.Section) is
            when Body_Part =>
               return Private_Scope (S);

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

      function Common_Ancestor (A, B : Flow_Scope) return Flow_Scope is
         L1  : constant Scope_Vectors.Vector := Heritage (A);
         L2  : constant Scope_Vectors.Vector := Heritage (B);

         Ptr : Natural := 0;
      begin
         loop
            if Count_Type (Ptr) = L1.Length or else
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

   --  Start of processing for Is_Initialized_At_Elaboration

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
            when E_Abstract_State |
                 E_Component      |
                 E_Constant       =>
               null;

            when E_Variable =>
               if Ekind (Etype (Ent)) in Concurrent_Kind then
                  --  Instances of a protected type are always fully default
                  --  initialized.
                  --  ??? arrays and record with protected types too
                  return True;
               elsif Is_Part_Of_Concurrent_Object (Ent) then
                  --  Variables that are Part_Of a concurrent type are always
                  --  fully default initialized.
                  return True;
               elsif not Is_Package_State (Ent) then
                  return False;
               end if;

            when E_Protected_Type =>
               --  Protected types are always fully default initialized in
               --  SPARK.
               return True;

            when E_Discriminant   =>
               --  Discriminants are always initialized
               return True;

            when others           =>
               Print_Tree_Node (Ent);
               raise Program_Error;
         end case;

         Init := Present (Find_Node_In_Initializes (Ent));

         if Ptr.Ent in Common_Scope.Ent | S.Ent then
            if Trace then
               Write_Line ("   -> in common scope or home");
            end if;

            if Ekind (Ent) = E_Variable and then
              Present (Encapsulating_State (Ent)) and then
              Get_Flow_Scope (Encapsulating_State (Ent)).Ent = Ptr.Ent
            then
               if Trace then
                  Write_Line ("   -> looking up");
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

   --------------------------------------------
   -- Mentions_State_With_Visible_Refinement --
   --------------------------------------------

   function Mentions_State_With_Visible_Refinement
     (N     : Node_Id;
      Scope : Flow_Scope)
      return Boolean
   is
      Found_State_Abstraction : Boolean := False;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Traversal procedure that sets Found_State_Abstraction to
      --  True if we find a State Abstraction whose refinement is
      --  visible from Scope.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Identifier
           and then Present (Entity (N))
           and then Ekind (Entity (N)) = E_Abstract_State
           and then State_Refinement_Is_Visible (Entity (N), Scope)
         then
            Found_State_Abstraction := True;
            return Abandon;
         end if;

         --  Keep looking...
         return OK;
      end Proc;

      procedure Look_For_Abstract_State is new Traverse_Proc (Process => Proc);

   --  Start of processing for Mentions_State_With_Visible_Refinement

   begin
      Look_For_Abstract_State (N);

      return Found_State_Abstraction;
   end Mentions_State_With_Visible_Refinement;

   -----------------------
   -- Refinement_Needed --
   -----------------------

   function Refinement_Needed (E : Entity_Id) return Boolean is
      Body_E : constant Entity_Id := Get_Body_Entity (E);

   begin
      if Present (Body_E) then
         declare
            Depends_N : constant Node_Id := Get_Pragma (E, Pragma_Depends);
            Global_N  : constant Node_Id := Get_Pragma (E, Pragma_Global);

            Refined_Depends_N : constant Node_Id :=
              Get_Pragma (Body_E, Pragma_Refined_Depends);
            Refined_Global_N  : constant Node_Id :=
              Get_Pragma (Body_E, Pragma_Refined_Global);

            B_Scope : constant Flow_Scope := Get_Flow_Scope (Body_E);

         begin
            return
              --  1) No Global and no Depends aspect
              (No (Global_N) and then No (Depends_N)) or else

              --  2) Global refers to state abstraction with visible refinement
              --     but no Refined_Global.
              (Present (Global_N) and then
                 No (Refined_Global_N) and then
                 No (Refined_Depends_N) and then
                 Mentions_State_With_Visible_Refinement (Global_N,
                                                         B_Scope)) or else

              --  3) Depends refers to state abstraction with visible
              --     refinement but no Refined_Depends.
              (Present (Depends_N) and then
                 No (Refined_Depends_N) and then
                 No (Refined_Global_N) and then
                 Mentions_State_With_Visible_Refinement (Depends_N, B_Scope));
         end;
      end if;

      return False;
   end Refinement_Needed;

   -------------------------------------
   -- Nested_Inside_Concurrent_Object --
   -------------------------------------

   function Nested_Inside_Concurrent_Object
     (CO : Entity_Id;
      S  : Flow_Scope)
      return Boolean
   is
      Context : Entity_Id := S.Ent;

   begin
      while Present (Context)
        and then Context /= Standard_Standard
      loop
         if Context = CO then
            return True;
         end if;
         Context := Scope (Context);
      end loop;

      return False;
   end Nested_Inside_Concurrent_Object;

end Flow_Refinement;
