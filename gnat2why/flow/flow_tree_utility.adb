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

         when N_Subprogram_Declaration =>
            return Corresponding_Body (P);

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
        Nkind (P) not in --  N_Function_Specification |
                         --  N_Procedure_Specification |
                         --  N_Package_Specification |
                         N_Subprogram_Body |
                         N_Package_Body
      loop
         P := Parent (P);
      end loop;
      return P;
   end Get_Enclosing_Scope;

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
         Scope_Of_Called_Subprogram := Get_Enclosing_Scope
           (Get_Enclosing_Scope (Body_E));
         P                          := Scope;

         while Present (P) and P /= Scope_Of_Called_Subprogram loop
            P := Get_Enclosing_Scope (P);
         end loop;
         return P = Scope_Of_Called_Subprogram;
      else
         --  If we have not parsed the body then clearly we need to
         --  use the abstract view.
         return False;
      end if;
   end Should_Use_Refined_View;

end Flow_Tree_Utility;
