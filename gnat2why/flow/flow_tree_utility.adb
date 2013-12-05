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

with Nlists;     use Nlists;
with Sem_Util;   use Sem_Util;
with Snames;     use Snames;
with Uintp;      use Uintp;

with SPARK_Util; use SPARK_Util;

with Why;

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

   ------------------------------
   -- Find_Node_In_Initializes --
   ------------------------------

   function Find_Node_In_Initializes (E : Entity_Id) return Node_Id is
      P  : Entity_Id := E;
      UE : constant Entity_Id := Unique_Entity (E);

      PAA      : Node_Id;
      Row, LHS : Node_Id;

   begin
      --  ??? Fix this to support refined state

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

      --  This code closely mirrors the one in Flow_Dependency_Maps,
      --  but I have not found a good way to refactor them.

      pragma Assert
        (List_Length (Pragma_Argument_Associations (P)) = 1);
      PAA := First (Pragma_Argument_Associations (P));
      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      case Nkind (Expression (PAA)) is
         when N_Null =>
            --  Aspect => null
            return Empty;

         when N_Aggregate =>
            --  Aspect => (...)

            --  We will deal with this in the following, in detail,
            --  extracting information from both the epxressions and
            --  component_associations of the aggregate.
            null;

         when N_Identifier =>
            --  Aspect => Foobar
            if Unique_Entity (Entity (Expression (PAA))) = UE then
               return Expression (PAA);
            end if;

         when others =>
            raise Why.Unexpected_Node;
      end case;

      pragma Assert_And_Cut (Nkind (Expression (PAA)) = N_Aggregate);
      --  Aspect => (...)

      --  First we should look at the expressions of the aggregate,
      --  i.e. foo and bar in (foo, bar, baz => ..., bork => ...)
      Row := First (Expressions (Expression (PAA)));
      while Present (Row) loop
         if Unique_Entity (Entity (Row)) = UE then
            return Row;
         end if;

         Row := Next (Row);
      end loop;

      --  Next, we look at the component associations, i.e. baz and
      --  bork in the above example.
      Row := First (Component_Associations (Expression (PAA)));
      while Present (Row) loop

         --  Process LHS (outputs)

         pragma Assert (List_Length (Choices (Row)) = 1);
         LHS := First (Choices (Row));
         case Nkind (LHS) is
            when N_Aggregate =>
               --  (Foo, Bar, Baz) => ...
               LHS := First (Expressions (LHS));
               while Present (LHS) loop
                  pragma Assert (Present (Entity (LHS)));
                  if Unique_Entity (Entity (LHS)) = UE then
                     return LHS;
                  end if;
                  LHS := Next (LHS);
               end loop;

            when N_Identifier | N_Expanded_Name =>
               --  Foo => ...
               pragma Assert (Present (Entity (LHS)));
               if Unique_Entity (Entity (LHS)) = UE then
                  return LHS;
               end if;

            when N_Null =>
               --  null => ...
               null;

            when others =>
               raise Why.Unexpected_Node;
         end case;

         --  Process RHS (inputs)
         --
         --  We're not interested in these for the purpose of finding
         --  entities which are initialized.

         --  Assemble map
         --
         --  Again, nothing to do here.

         Row := Next (Row);
      end loop;

      return Empty;
   end Find_Node_In_Initializes;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (E : Entity_Id) return Boolean is
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return Find_Node_In_Initializes (E) /= Empty or else
              (Present (Encapsulating_State (E)) and then
                 Is_Initialized_At_Elaboration (Encapsulating_State (E)));

         when E_Variable =>
            if Is_Package_State (E) then
               if Present (Encapsulating_State (E)) then
                  return
                    Is_Initialized_At_Elaboration (Encapsulating_State (E));
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

   -----------------------------
   -- Last_Statement_Is_Raise --
   -----------------------------

   function Last_Statement_Is_Raise (E : Entity_Id) return Boolean is
      The_Body       : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
      Last_Statement : constant Node_Id :=
        Last (Statements (Handled_Statement_Sequence (The_Body)));
   begin
      return (Nkind (Last_Statement) = N_Raise_Statement
                or else Nkind (Last_Statement) in N_Raise_xxx_Error);
   end Last_Statement_Is_Raise;

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

end Flow_Tree_Utility;
