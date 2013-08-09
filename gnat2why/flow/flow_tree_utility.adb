------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 B o d y                                  --
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

with Sem_Util; use Sem_Util;
with Snames;   use Snames;
with Uintp;    use Uintp;
with Nlists;   use Nlists;

with Why;

--  with Treepr; use Treepr;
--  with Output; use Output;

package body Flow_Tree_Utility is

   --------------------------------
   -- Lexicographic_Entity_Order --
   --------------------------------

   function Lexicographic_Entity_Order (Left, Right : Node_Id)
                                        return Boolean is
   begin
      return Unique_Name (Left) < Unique_Name (Right);
   end Lexicographic_Entity_Order;

   -----------------------------------
   -- Contains_Loop_Entry_Reference --
   -----------------------------------

   function Contains_Loop_Entry_Reference (N : Node_Id) return Boolean
   is
      Found_Loop_Entry : Boolean := False;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Sets found_loop_entry if the N is a loop_entry attribute
      --  reference.

      function Proc (N : Node_Id) return Traverse_Result
      is
      begin
         case Nkind (N) is
            when N_Attribute_Reference =>
               if Get_Attribute_Id (Attribute_Name (N)) =
                 Attribute_Loop_Entry
               then
                  Found_Loop_Entry := True;
                  return Abandon;
               else
                  return OK;
               end if;

            when others =>
               return OK;
         end case;
      end Proc;

      procedure Search_For_Loop_Entry is new Traverse_Proc (Proc);
   begin
      Search_For_Loop_Entry (N);
      return Found_Loop_Entry;
   end Contains_Loop_Entry_Reference;

   ---------------------------------
   -- Get_Procedure_Specification --
   ---------------------------------

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id
   is
      N : Node_Id;
   begin
      N := Parent (E);
      case Nkind (N) is
         when N_Defining_Program_Unit_Name =>
            return Parent (N);
         when N_Procedure_Specification =>
            return N;
         when others =>
            raise Program_Error;
      end case;
   end Get_Procedure_Specification;

   -------------------
   -- Might_Be_Main --
   -------------------

   function Might_Be_Main (E : Entity_Id) return Boolean
   is
   begin
      return (Scope_Depth_Value (E) = Uint_1 or else
                (Is_Generic_Instance (E) and then
                   Scope_Depth_Value (E) = Uint_2))
        and then No (First_Formal (E));
   end Might_Be_Main;

   ------------------------------
   -- Find_Node_In_Initializes --
   ------------------------------

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id
   is
      P : Entity_Id := E;
   begin
      --  !!! Fix this to support refined state

      while Ekind (P) /= E_Package loop
         case Ekind (P) is
            when E_Package_Body =>
               raise Why.Not_Implemented;
            when others =>
               P := Scope (P);
         end case;
      end loop;
      P := Get_Pragma (P, Pragma_Initializes);
      if not Present (P) then
         return Empty;
      end if;

      pragma Assert (List_Length (Pragma_Argument_Associations (P)) = 1);
      P := First (Pragma_Argument_Associations (P));
      P := Expression (P);
      case Nkind (P) is
         when N_Aggregate =>
            if Present (Expressions (P)) then
               P := First (Expressions (P));
               while Present (P) loop
                  case Nkind (P) is
                     when N_Identifier | N_Expanded_Name =>
                        if Entity (P) = E then
                           return P;
                        end if;
                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
                  P := Next (P);
               end loop;
            elsif Present (Component_Associations (P)) then
               P := First (Component_Associations (P));
               while Present (P) loop
                  pragma Assert (List_Length (Choices (P)) = 1);
                  if Entity (First (Choices (P))) = E then
                     return First (Choices (P));
                  end if;
                  P := Next (P);
               end loop;
            else
               raise Why.Unexpected_Node;
            end if;

            return Empty;

         when N_Identifier | N_Expanded_Name =>
            if Entity (P) = E then
               return P;
            else
               return Empty;
            end if;

         when others =>
            raise Why.Unexpected_Node;
      end case;
   end Find_Node_In_Initializes;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (E : Entity_Id) return Boolean
   is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return Find_Node_In_Initializes (E) /= Empty;

         when E_Variable =>
            if Is_Package_State (E) then
               if Present (Refined_State (E)) then
                  return Is_Initialized_At_Elaboration (Refined_State (E));
               else
                  return Find_Node_In_Initializes (E) /= Empty;
               end if;
            else
               return False;
            end if;

         when others =>
            return False;
      end case;
   end Is_Initialized_At_Elaboration;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean
   is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return True;

         when E_Variable =>
            case Ekind (Scope (E)) is
               when E_Package =>
                  return True;

               when others =>
                  return False;
            end case;

         when others =>
            return False;

      end case;
   end Is_Package_State;

   --------------
   -- Get_Body --
   --------------

   function Get_Body (E : Entity_Id) return Entity_Id
   is
      P : constant Node_Id := Parent (Parent (E));
   begin
      case Nkind (P) is
         when N_Subprogram_Body =>
            pragma Assert (Acts_As_Spec (P));
            return Empty;

         when N_Subprogram_Declaration | N_Subprogram_Body_Stub =>
            return Corresponding_Body (P);

         when N_Formal_Concrete_Subprogram_Declaration =>
            --  We should only get here from Magic_String_To_Node_Sets
            return Empty;

         when others =>
            raise Why.Unexpected_Node;
      end case;
   end Get_Body;

   -------------------------
   -- Get_Enclosing_Scope --
   -------------------------

   function Get_Enclosing_Scope (N : Node_Id) return Scope_Ptr
   is
      P : Node_Id := Parent (N);
   begin
      while Present (P) and then
        Nkind (P) not in N_Function_Specification |
                         N_Procedure_Specification |
                         N_Package_Specification |
                         N_Subprogram_Body |
                         N_Package_Body
      loop
         P := Parent (P);
      end loop;
      return P;
   end Get_Enclosing_Scope;

   ------------------------------
   -- Get_Enclosing_Body_Scope --
   ------------------------------

   function Get_Enclosing_Body_Scope (N : Node_Id) return Scope_Ptr
   is
      P : Node_Id := Parent (N);
   begin
      while Present (P) and then
        Nkind (P) not in N_Subprogram_Body |
                         N_Package_Body
      loop
         P := Parent (P);
      end loop;
      return P;
   end Get_Enclosing_Body_Scope;

   -----------------------------
   -- Should_Use_Refined_View --
   -----------------------------

   function Should_Use_Refined_View (Scope : Scope_Ptr;
                                     N     : Node_Id)
                                     return Boolean
   is
      Spec_E : constant Node_Id := Entity (Name (N));
      Body_E : constant Node_Id := Get_Body (Spec_E);

      Scope_Of_Called_Subprogram : Scope_Ptr;
      P                          : Scope_Ptr;
   begin
      --  !!! To be resolved completely in M314-012 once M619-012 is
      --  !!! answered.
      if Present (Body_E) then
         Scope_Of_Called_Subprogram := Get_Enclosing_Body_Scope
           (Get_Enclosing_Body_Scope (Body_E));
         P                          := Scope;

         while Present (P) and P /= Scope_Of_Called_Subprogram loop
            P := Get_Enclosing_Body_Scope (P);
         end loop;
         return P = Scope_Of_Called_Subprogram;
      else
         --  If we have not parsed the body then clearly we need to
         --  use the abstract view.
         return False;
      end if;
   end Should_Use_Refined_View;

   -----------------------------
   -- Last_Statement_Is_Raise --
   -----------------------------

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean is
      The_Body       : Node_Id;
      Last_Statement : Node_Id;
   begin
      --  Expression functions cannot have a raise statement as their last
      --  statement (all they have is a single statement).
      if Is_Expression_Function (E) then
         return False;
      end if;

      if Is_Generic_Instance (E) then
         declare
            Associated_Generic : constant Node_Id :=
              Parent (Parent (Generic_Parent (Parent (E))));
         begin
            if Present (Corresponding_Body (Associated_Generic)) then
               The_Body :=
                 Parent (Parent (Corresponding_Body (Associated_Generic)));
            else
               return False;
            end if;
         end;
      else
         The_Body := Parent (Parent (E));

         if Nkind (The_Body) = N_Subprogram_Declaration then
            if Present (Corresponding_Body (The_Body)) then
               The_Body := Parent (Parent (Corresponding_Body (The_Body)));
            else
               return False;
            end if;
         end if;
      end if;

      Last_Statement :=
        Last (Statements (Handled_Statement_Sequence (The_Body)));

      return (Nkind (Last_Statement) = N_Raise_Statement
                or else Nkind (Last_Statement) in N_Raise_xxx_Error);
   end Last_Statement_Is_Raise;

end Flow_Tree_Utility;
