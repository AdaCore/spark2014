------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                     F L O W . R E F I N E M E N T                        --
--                                                                          --
--                                B o d y                                   --
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

with Elists;   use Elists;
with Nlists;   use Nlists;
with Snames;   use Snames;
with Stand;    use Stand;

with Flow_Tree_Utility; use Flow_Tree_Utility;

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
   --  Returns true iff the target scope is visible from S.

   function Is_Visible (N : Node_Id;
                        S : Flow_Scope)
                        return Boolean;
   --  Returns true iff the node N is visible from the scope S.

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
      Ptr : Flow_Scope := S;
   begin
      while Ptr /= Null_Flow_Scope loop
         if Ptr = Target_Scope then
            return True;
         end if;

         case Valid_Section_T'(Ptr.Section) is
            when Body_Part =>
               Ptr.Section := Private_Part;

            when Private_Part =>
               if Flow_Scope'(Ptr.Pkg, Spec_Part) = Target_Scope then
                  return True;
               end if;
               Ptr := Get_Enclosing_Flow_Scope (Ptr);

            when Spec_Part =>
               Ptr := Get_Enclosing_Flow_Scope (Ptr);
         end case;
      end loop;

      return False;
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
   begin
      declare
         Ptr : Node_Id := S.Pkg;
      begin
         while Nkind (Ptr) /= N_Package_Declaration loop
            Ptr := Parent (Ptr);
         end loop;
         Enclosing_Scope := Get_Flow_Scope (Ptr);

         if Enclosing_Scope = Null_Flow_Scope and then
           Scope (S.Pkg) /= Standard_Standard
         then
            Enclosing_Scope := Flow_Scope'(Scope (S.Pkg), S.Section);
         end if;
      end;

      if Is_Private_Descendant (S.Pkg) then
         Enclosing_Scope.Section := Private_Part;
      end if;

      return Enclosing_Scope;
   end Get_Enclosing_Flow_Scope;

   --------------------
   -- Get_Flow_Scope --
   --------------------

   function Get_Flow_Scope (N : Node_Id) return Flow_Scope
   is
      P : Node_Id;
      V : Section_T;
   begin
      P := N;
      while Present (P) loop
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
               if Tree_Contains (Private_Declarations (P), N) then
                  V := Private_Part;
               else
                  V := Spec_Part;
               end if;
               P := Defining_Unit_Name (P);
               if Nkind (P) = N_Defining_Program_Unit_Name then
                  P := Defining_Identifier (P);
               end if;
               exit;

            when others =>
               null;
         end case;

         P := Parent (P);
      end loop;

      if Present (P) then
         return Flow_Scope'(P, V);
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

      return Is_Visible (Body_E, S);
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
           (Body_E, (case C is
                        when Global_Contract => Pragma_Refined_Global,
                        when Depends_Contract => Pragma_Refined_Depends));
      end if;

      if No (N) then
         N := Get_Pragma
           (E, (case C is
                   when Global_Contract => Pragma_Global,
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
      --  We return either E if its refinement is not visible, and all
      --  consitituents of E otherwise.
      --
      --  If E is not abstract state, we also just return V.

      ------------
      -- Expand --
      ------------

      function Expand (E : Entity_Id) return Node_Sets.Set
      is
         Tmp : Node_Sets.Set := Node_Sets.Empty_Set;
         Ptr : Elmt_Id;
      begin
         case Ekind (E) is
            when E_Abstract_State =>
               if State_Refinement_Is_Visible (E, S) then
                  Ptr := First_Elmt (Refinement_Constituents (E));
                  while Present (Ptr) loop
                     Tmp.Union (Expand (Node (Ptr)));
                     Ptr := Next_Elmt (Ptr);
                  end loop;

                  Ptr := First_Elmt (Part_Of_Constituents (E));
                  while Present (Ptr) loop
                     Tmp.Union (Expand (Node (Ptr)));
                     Ptr := Next_Elmt (Ptr);
                  end loop;

               else
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

end Flow_Refinement;
