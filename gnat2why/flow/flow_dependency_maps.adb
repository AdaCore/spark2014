------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
--                                                                          --
--                                 B o d y                                  --
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

with Elists;                         use Elists;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                   use Flow_Utility;
with Nlists;                         use Nlists;
with Sinfo;                          use Sinfo;
with SPARK_Util;                     use SPARK_Util;
with Treepr;                         use Treepr;
with Why;

package body Flow_Dependency_Maps is

   use Dependency_Maps;

   function Parse_Raw_Dependency_Map (N : Node_Id) return Dependency_Maps.Map
   with Pre => Get_Pragma_Id (N) in
                 Pragma_Depends         |
                 Pragma_Refined_Depends |
                 Pragma_Refined_State   |
                 Pragma_Initializes;
   --  Helper function to parse something that looks like a dependency map; in
   --  particular we can parse either a depends or an initializes aspect.
   --
   --  Generic formals without variable input are excluded from the returned
   --  map.

   ------------------------------
   -- Parse_Raw_Dependency_Map --
   ------------------------------

   function Parse_Raw_Dependency_Map (N : Node_Id) return Dependency_Maps.Map
   is
      pragma Assert (List_Length (Pragma_Argument_Associations (N)) = 1);

      PAA : constant Node_Id := First (Pragma_Argument_Associations (N));

      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      Expr : constant Node_Id := Expression (PAA);

      M : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;

      Inputs  : Flow_Id_Sets.Set;
      Outputs : Flow_Id_Sets.Set;
   begin
      case Nkind (Expr) is
         when N_Aggregate =>
            --  Aspect => (...)

            --  We will deal with this in the following, in detail,
            --  extracting information from both the epxressions and
            --  component_associations of the aggregate.
            null;

         when N_Identifier =>
            --  Aspect => Foobar
            M.Insert (Direct_Mapping_Id (Expr),
                      Flow_Id_Sets.Empty_Set);
            return M;

         when N_Null =>
            --  Aspect => null
            return M;

         when others =>
            raise Why.Unexpected_Node;
      end case;

      pragma Assert_And_Cut (Nkind (Expr) = N_Aggregate);
      --  Aspect => (...)

      --  First, we look at the expressions of the aggregate, i.e. foo and bar
      --  in (foo, bar, baz => ..., bork => ...).
      Row := First (Expressions (Expr));
      while Present (Row) loop
         declare
            E : constant Entity_Id := Entity (Original_Node (Row));
         begin
            M.Insert (Direct_Mapping_Id (Unique_Entity (E)),
                      Flow_Id_Sets.Empty_Set);
         end;
         Row := Next (Row);
      end loop;

      --  Next, we look at the component associations, i.e. baz and bork in the
      --  above example.
      Row := First (Component_Associations (Expr));
      while Present (Row) loop
         Inputs  := Flow_Id_Sets.Empty_Set;
         Outputs := Flow_Id_Sets.Empty_Set;

         --  Processing for LHS (outputs) and RHS (inputs) is almost identical,
         --  except for few special cases. It seems good to leave this code
         --  like this, since it offers more protection against malformed AST.

         --  Process LHS (outputs)

         pragma Assert (List_Length (Choices (Row)) = 1);
         LHS := First (Choices (Row));
         case Nkind (LHS) is
            when N_Aggregate =>
               --  (Foo, Bar, Baz) => ...
               LHS := First (Expressions (LHS));
               while Present (LHS) loop
                  Outputs.Include
                    (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));
                  LHS := Next (LHS);
               end loop;

            when N_Attribute_Reference =>
               --  foo'result => ...
               pragma Assert (Ekind (Entity (Prefix (LHS))) = E_Function);

               pragma Assert (Get_Attribute_Id (Attribute_Name (LHS)) =
                                Attribute_Result);

               Outputs.Include
                 (Direct_Mapping_Id (Entity (Prefix (LHS))));

            when N_Identifier | N_Expanded_Name =>
               --  Foo => ...
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));

            when N_Null =>
               --  null => ...
               null;

            when N_Numeric_Or_String_Literal =>
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Original_Constant (LHS))));

            when others =>
               Print_Node_Subtree (LHS);
               raise Why.Unexpected_Node;
         end case;

         --  Process RHS (inputs)

         RHS := Expression (Row);
         case Nkind (RHS) is
            when N_Aggregate =>
               RHS := First (Expressions (RHS));
               while Present (RHS) loop
                  Inputs.Include
                    (Direct_Mapping_Id
                       (Unique_Entity
                          (if Nkind (RHS) in N_Numeric_Or_String_Literal
                           then Original_Constant (RHS)
                           else Entity (RHS))));

                  RHS := Next (RHS);
               end loop;

            when N_Identifier | N_Expanded_Name =>
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));

            when N_Null =>
               null;

            when N_Numeric_Or_String_Literal =>
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Original_Constant (RHS))));

            when others =>
               Print_Node_Subtree (RHS);
               raise Why.Unexpected_Node;

         end case;

         --  Filter out generic formals without variable output
         Remove_Constants (Inputs, Only_Generic_Formals => True);

         --  Assemble map

         if Outputs.Is_Empty then
            --  Update map only if both Inputs are present; otherwise do
            --  nothing, since both Outputs and Inputs are empty.
            if not Inputs.Is_Empty then
               --  No explicit outputs means null
               M.Insert (Key => Null_Flow_Id, New_Item => Inputs);
            end if;
         else
            for Output of Outputs loop
               M.Insert (Key => Output, New_Item => Inputs);
            end loop;
         end if;

         Row := Next (Row);
      end loop;

      return M;
   end Parse_Raw_Dependency_Map;

   -------------------
   -- Parse_Depends --
   -------------------

   function Parse_Depends
     (N : Node_Id)
      return Dependency_Maps.Map renames
     Parse_Raw_Dependency_Map;

   -----------------------
   -- Parse_Initializes --
   -----------------------

   function Parse_Initializes
     (P : Entity_Id;
      S : Flow_Scope)
      return Dependency_Maps.Map
   is
      Initializes  : constant Node_Id  := Get_Pragma (P, Pragma_Initializes);
      Abstr_States : constant Elist_Id := Abstract_States (P);

      M : Dependency_Maps.Map;

   begin
      --  If an initializes aspect exists then we use it
      if Present (Initializes) then
         M := Parse_Raw_Dependency_Map (Initializes);

      --  If an initializes aspect does not exist but the global generation
      --  phase has been completed then look for the generated initializes.

      elsif GG_Has_Been_Generated then
         M := GG_Get_Initializes (P, S);

      --  There is neither a user-provided nor a generated initializes aspect
      --  so we just leave the empty dependency map as it is.

      else
         null;

      end if;

      --  Add any external state abstractions with Async_Writers property to
      --  the dependency map (even if they are not in the user's annotations).
      --  This ensures that constituents that are volatile with Async_Writers
      --  flavour are also initialized.
      if Present (Abstr_States) then
         declare
            State_Elmt : Elmt_Id;
            State      : Entity_Id;

            Position : Dependency_Maps.Cursor;
            Inserted : Boolean;
            --  Dummy values required by Hashed_Sets API

         begin
            State_Elmt := First_Elmt (Abstr_States);
            State      := Node (State_Elmt);

            --  If it is just a null state then do nothing

            if not Is_Null_State (State) then
               loop
                  if Has_Volatile (State)
                    and then Has_Volatile_Flavor (State, Pragma_Async_Writers)
                  then
                     --  Try to insert an empty set, do nothing if another
                     --  value is already in the map.
                     M.Insert (Key      => Direct_Mapping_Id (State),
                               Position => Position,
                               Inserted => Inserted);
                  end if;

                  --  Move on to the next state abstraction
                  Next_Elmt (State_Elmt);
                  State := Node (State_Elmt);

                  exit when No (State);
               end loop;
            end if;
         end;
      end if;

      return M;
   end Parse_Initializes;

   -------------------------
   -- Parse_Refined_State --
   -------------------------

   function Parse_Refined_State
     (N : Node_Id)
      return Dependency_Maps.Map renames
     Parse_Raw_Dependency_Map;

end Flow_Dependency_Maps;
