------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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

with Common_Containers;      use Common_Containers;
with Einfo;                  use Einfo;
with Elists;                 use Elists;
with Flow_Generated_Globals; use Flow_Generated_Globals;
with Flow_Utility;           use Flow_Utility;
with Nlists;                 use Nlists;
with Treepr;                 use Treepr;
with Why;

package body Flow_Dependency_Maps is

   use Dependency_Maps;

   function Parse_Raw_Dependency_Map (N : Node_Id) return Dependency_Maps.Map
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (Chars (Pragma_Identifier (N))) in
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

      M : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;

      Inputs  : Flow_Id_Sets.Set;
      Outputs : Flow_Id_Sets.Set;
   begin
      case Nkind (Expression (PAA)) is
         when N_Aggregate =>
            --  Aspect => (...)

            --  We will deal with this in the following, in detail,
            --  extracting information from both the epxressions and
            --  component_associations of the aggregate.
            null;

         when N_Identifier =>
            --  Aspect => Foobar
            M.Include (Direct_Mapping_Id (Expression (PAA)),
                       Flow_Id_Sets.Empty_Set);
            return M;

         when N_Null =>
            --  Aspect => null
            return M;

         when others =>
            raise Why.Unexpected_Node;
      end case;

      pragma Assert_And_Cut (Nkind (Expression (PAA)) = N_Aggregate);
      --  Aspect => (...)

      --  First we should look at the expressions of the aggregate,
      --  i.e. foo and bar in (foo, bar, baz => ..., bork => ...)
      Row := First (Expressions (Expression (PAA)));
      while Present (Row) loop
         declare
            E : constant Entity_Id := Entity (Original_Node (Row));
         begin
            M.Include (Direct_Mapping_Id (Unique_Entity (E)),
                       Flow_Id_Sets.Empty_Set);
         end;
         Row := Next (Row);
      end loop;

      --  Next, we look at the component associations, i.e. baz and
      --  bork in the above example.
      Row := First (Component_Associations (Expression (PAA)));
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
                  pragma Assert (Present (Entity (LHS)));
                  Outputs.Include
                    (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));
                  LHS := Next (LHS);
               end loop;

            when N_Attribute_Reference =>
               --  foo'result => ...
               pragma Assert (Present (Entity (Prefix (LHS))));
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (Prefix (LHS)))));

            when N_Identifier | N_Expanded_Name =>
               --  Foo => ...
               pragma Assert (Present (Entity (LHS)));
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));

            when N_Null =>
               --  null => ...
               null;

            when N_Numeric_Or_String_Literal =>
               --  We should only ever get here if we are dealing with
               --  a rewritten constant.
               pragma Assert (LHS /= Original_Node (LHS));

               --  We process the entity of the Original_Node instead
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity
                                       (Entity (Original_Node (LHS)))));

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
                  if Nkind (RHS) in N_Numeric_Or_String_Literal then
                     --  We should only ever get here if we are
                     --  dealing with a rewritten constant.
                     pragma Assert (RHS /= Original_Node (RHS));
                     Inputs.Include
                       (Direct_Mapping_Id
                          (Unique_Entity (Entity (Original_Node (RHS)))));
                  else
                     pragma Assert (Present (Entity (RHS)));
                     Inputs.Include
                       (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));
                  end if;
                  RHS := Next (RHS);
               end loop;

            when N_Identifier | N_Expanded_Name =>
               pragma Assert (Present (Entity (RHS)));
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));

            when N_Null =>
               null;

            when N_Numeric_Or_String_Literal =>
               --  We should only ever get here if we are dealing with
               --  a rewritten constant.
               pragma Assert (RHS /= Original_Node (RHS));

               --  We process the entity of the Original_Node instead
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity
                                       (Entity (Original_Node (RHS)))));

            when others =>
               Print_Node_Subtree (RHS);
               raise Why.Unexpected_Node;

         end case;

         --  Filter out generic formals without variable output

         Inputs := Filter_Out_Constants (Inputs,
                                         Node_Sets.Empty_Set,
                                         True);
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
     (N : Node_Id;
      P : Entity_Id;
      S : Flow_Scope)
      return Dependency_Maps.Map
   is
      M : Dependency_Maps.Map;
   begin
      if Present (N) then
         --  If an initializes aspect exists then we use it
         M := Parse_Raw_Dependency_Map (N);
      elsif GG_Has_Been_Generated
        and then Present (P)
      then
         --  If an initializes aspect does not exist but the global generation
         --  phase has been completed then we look for the generate
         --  initializes.
         M := GG_Get_Initializes (To_Entity_Name (Unique_Entity (P)), S);
      else
         --  We have neither a user-provided nor a generated initializes aspect
         --  so we just have an empty dependency map.
         M := Dependency_Maps.Empty_Map;
      end if;

      --  When we parse the Initializes aspect we add any external
      --  state abstractions with the property Async_Writers set to
      --  the dependency map (even if the user did not manually write
      --  them there). This is to ensure that constituents that are
      --  not volatile and have Async_Writers are also initialized.
      if Present (P)
        and then Ekind (P) in E_Generic_Package | E_Package
        and then Present (Abstract_States (P))
        and then not Is_Null_State (Node (First_Elmt (Abstract_States (P))))
      then
         declare
            State_Elmt : Elmt_Id;
            State      : Entity_Id;
         begin
            State_Elmt := First_Elmt (Abstract_States (P));
            State      := Node (State_Elmt);

            while Present (State) loop
               if Has_Async_Writers (Direct_Mapping_Id (State))
                 and then not M.Contains (Direct_Mapping_Id (State))
               then
                  M.Insert (Direct_Mapping_Id (State), Flow_Id_Sets.Empty_Set);
               end if;

               --  Move on to the next state abstraction
               Next_Elmt (State_Elmt);
               State := Node (State_Elmt);
            end loop;
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
