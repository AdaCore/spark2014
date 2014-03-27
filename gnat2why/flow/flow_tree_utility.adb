------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W _ T R E E _ U T I L I T Y                     --
--                                                                          --
--                                 B o d y                                  --
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

with Sem_Util;   use Sem_Util;
with Uintp;      use Uintp;

with Treepr;     use Treepr;

with Why;
--  For the exceptions

package body Flow_Tree_Utility is

   --------------------------------
   -- Lexicographic_Entity_Order --
   --------------------------------

   function Lexicographic_Entity_Order
     (Left, Right : Node_Id) return Boolean is
   begin
      return Unique_Name (Left) < Unique_Name (Right);
   end Lexicographic_Entity_Order;

   -----------------------------------
   -- Contains_Loop_Entry_Reference --
   -----------------------------------

   function Contains_Loop_Entry_Reference (N : Node_Id) return Boolean is
      Found_Loop_Entry : Boolean := False;

      function Proc (N : Node_Id) return Traverse_Result;
      --  Sets found_loop_entry if the N is a loop_entry attribute
      --  reference.

      function Proc (N : Node_Id) return Traverse_Result is
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

   function Get_Procedure_Specification (E : Entity_Id) return Node_Id is
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

   function Might_Be_Main (E : Entity_Id) return Boolean is
   begin
      return (Scope_Depth_Value (E) = Uint_1 or else
                (Is_Generic_Instance (E) and then
                   Scope_Depth_Value (E) = Uint_2))
        and then No (First_Formal (E));
   end Might_Be_Main;

   ----------------------
   -- Is_Package_State --
   ----------------------

   function Is_Package_State (E : Entity_Id) return Boolean is
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

   function Get_Body (E : Entity_Id) return Entity_Id is
      P : Node_Id := Parent (E);
   begin
      if Nkind (P) = N_Defining_Program_Unit_Name then
         P := Parent (P);
      end if;

      P := Parent (P);

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

   -------------------
   -- Get_Enclosing --
   -------------------

   function Get_Enclosing (N : Node_Id; K : Node_Kind) return Node_Id
   is
      Ptr : Node_Id := N;
   begin
      while Present (Ptr) and then Nkind (Ptr) /= K loop
         Ptr := Parent (Ptr);
      end loop;
      return Ptr;
   end Get_Enclosing;

   ------------------
   -- Has_Volatile --
   ------------------

   function Has_Volatile (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return Is_External_State (E);
         when Type_Kind =>
            return Is_Volatile (E);
         when others =>
            return Is_Volatile (E) or else Has_Volatile (Etype (E));
      end case;
   end Has_Volatile;

   -------------------------
   -- Has_Volatile_Aspect --
   -------------------------

   function Has_Volatile_Aspect (E : Entity_Id;
                                 A : Pragma_Id)
                                 return Boolean
   is
      function Has_Specific_Aspect (E : Entity_Id) return Boolean
      is (Present (Get_Pragma (E, Pragma_Async_Readers)) or else
            Present (Get_Pragma (E, Pragma_Async_Writers)) or else
            Present (Get_Pragma (E, Pragma_Effective_Reads)) or else
            Present (Get_Pragma (E, Pragma_Effective_Writes)));
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            case A is
               when Pragma_Async_Writers =>
                  return Async_Writers_Enabled (E);
               when Pragma_Effective_Reads =>
                  return Effective_Reads_Enabled (E);
               when Pragma_Async_Readers =>
                  return Async_Readers_Enabled (E);
               when Pragma_Effective_Writes =>
                  return Effective_Writes_Enabled (E);
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Parameter =>
            case A is
               when Pragma_Async_Writers =>
                  return True;
               when Pragma_Async_Readers    |
                    Pragma_Effective_Reads  |
                    Pragma_Effective_Writes =>
                  return False;
               when others =>
                  raise Program_Error;
            end case;

         when E_Out_Parameter =>
            case A is
               when Pragma_Async_Writers | Pragma_Effective_Reads =>
                  return False;
               when Pragma_Async_Readers | Pragma_Effective_Writes =>
                  return True;
               when others =>
                  raise Program_Error;
            end case;

         when E_In_Out_Parameter =>
            return True;

         when E_Variable =>
            if Present (Get_Pragma (E, A)) then
               return True;
            elsif Has_Specific_Aspect (E) then
               return False;
            else
               return True;
            end if;

         when E_Constant =>
            --  SRM 7.1.3(6): A constant, a discriminant or a loop
            --  parameter shall not be Volatile.
            return False;

         when others =>
            Print_Tree_Node (E);
            raise Why.Unexpected_Node;
      end case;
   end Has_Volatile_Aspect;

end Flow_Tree_Utility;
