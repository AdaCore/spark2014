------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2020, Altran UK Limited                --
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

with Common_Containers;              use Common_Containers;
with Common_Iterators;               use Common_Iterators;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                   use Flow_Utility;
with Nlists;                         use Nlists;
with Sem_Prag;                       use Sem_Prag;
with Sinfo;                          use Sinfo;
with SPARK_Util;                     use SPARK_Util;

package body Flow_Dependency_Maps is

   function Parse_Raw_Dependency_Map (N : Node_Id) return Dependency_Maps.Map
   with Pre => Get_Pragma_Id (N) in Pragma_Depends
                                  | Pragma_Refined_Depends
                                  | Pragma_Initializes;
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
      Decl_Id : constant Entity_Id :=
        Defining_Entity (Find_Related_Declaration_Or_Body (N));
      --  Declaration of the entity to which the parsed pragma is attached

      Context : constant Entity_Id :=
        (if Is_Single_Task_Object (Decl_Id)
         then Etype (Decl_Id)
         else Unique_Entity (Decl_Id));
      --  Entity associated with the pragma of the parsed map. Needed to
      --  substitute references to a current single concurrent object (which
      --  are convenient for the frontend) with references to the corresponding
      --  current concurrent type (which are convenient for GNATprove).

      pragma Assert (List_Length (Pragma_Argument_Associations (N)) = 1);

      PAA : constant Node_Id := First (Pragma_Argument_Associations (N));

      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      Expr : constant Node_Id := Expression (PAA);

      M : Dependency_Maps.Map;

      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;

      Inputs  : Node_Sets.Set;
      Outputs : Flow_Id_Sets.Set;

   --  Start of processing for Parse_Raw_Dependency_Map

   begin
      --  Aspect is written either as:
      --  * "Aspect => null"
      --  * "Aspect => foo" (but this is translated into "Aspect => (foo)")
      --  * "Aspect => (...)"

      if Nkind (Expr) = N_Null then
         return Dependency_Maps.Empty_Map;
      end if;

      pragma Assert_And_Cut (Nkind (Expr) = N_Aggregate);

      --  First, we look at the expressions of the aggregate, i.e. foo and bar
      --  in (foo, bar, baz => ..., bork => ...).
      Row := First (Expressions (Expr));
      while Present (Row) loop
         declare
            E : constant Entity_Id := Entity (Original_Node (Row));

         begin
            M.Insert (Direct_Mapping_Id (Canonical_Entity (E, Context)),
                      Flow_Id_Sets.Empty_Set);
         end;
         Next (Row);
      end loop;

      --  Next, we look at the component associations, i.e. baz and bork in the
      --  above example.
      Row := First (Component_Associations (Expr));
      while Present (Row) loop
         Inputs.Clear;
         Outputs.Clear;

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
                  Outputs.Insert
                    (Direct_Mapping_Id
                       (Canonical_Entity (Entity (LHS), Context)));
                  Next (LHS);
               end loop;

            when N_Attribute_Reference =>
               --  foo'result => ...
               pragma Assert (Ekind (Entity (Prefix (LHS))) = E_Function);

               pragma Assert (Get_Attribute_Id (Attribute_Name (LHS)) =
                                Attribute_Result);

               Outputs.Insert
                 (Direct_Mapping_Id (Entity (Prefix (LHS))));

            when N_Identifier | N_Expanded_Name =>
               --  Foo => ...
               Outputs.Insert
                 (Direct_Mapping_Id
                    (Canonical_Entity (Entity (LHS), Context)));

            when N_Null =>
               --  null => ...
               null;

            when others =>
               raise Program_Error;
         end case;

         --  Process RHS (inputs)

         RHS := Expression (Row);
         case Nkind (RHS) is
            when N_Aggregate =>
               RHS := First (Expressions (RHS));
               while Present (RHS) loop
                  declare
                     E : constant Entity_Id :=
                       Canonical_Entity (Entity (RHS), Context);

                  begin
                     if not Is_Generic_Actual_Without_Variable_Input (E) then
                        Inputs.Insert (E);
                     end if;
                  end;

                  Next (RHS);
               end loop;

            when N_Identifier | N_Expanded_Name =>
               declare
                  E : constant Entity_Id :=
                    Canonical_Entity (Entity (RHS), Context);

               begin
                  if not Is_Generic_Actual_Without_Variable_Input (E) then
                     Inputs.Insert (E);
                  end if;
               end;

            when N_Null =>
               null;

            when others =>
               raise Program_Error;

         end case;

         --  Assemble map

         if Outputs.Is_Empty then
            --  Update map only if both Inputs are present; otherwise do
            --  nothing, since both Outputs and Inputs are empty.
            if not Inputs.Is_Empty then
               --  No explicit outputs means null
               M.Insert (Key      => Null_Flow_Id,
                         New_Item => To_Flow_Id_Set (Inputs));
            end if;
         else
            for Output of Outputs loop
               M.Insert (Key      => Output,
                         New_Item => To_Flow_Id_Set (Inputs));
            end loop;
         end if;

         Next (Row);
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
     (P    : Entity_Id;
      Scop : Flow_Scope)
      return Dependency_Maps.Map
   is
      Initializes : constant Node_Id := Get_Pragma (P, Pragma_Initializes);

      M : Dependency_Maps.Map;

   begin
      --  If an initializes aspect exists then we use it
      if Present (Initializes) then
         M := Parse_Raw_Dependency_Map (Initializes);

      --  If an initializes aspect does not exist but the global generation
      --  phase has been completed then look for the generated initializes.

      elsif GG_Has_Been_Generated then
         M := GG_Get_Initializes (P);

      --  There is neither a user-provided nor a generated initializes aspect
      --  so we just leave the empty dependency map as it is.

      else
         null;

      end if;

      --  Add any external state abstractions with Async_Writers property to
      --  the dependency map (even if they are not in the user's annotations).
      --  This ensures that constituents that are volatile with Async_Writers
      --  property are also initialized.
      if Has_Non_Null_Abstract_State (P) then
         for State of Iter (Abstract_States (P)) loop
            if Has_Volatile (State)
              and then Has_Volatile_Property (State, Pragma_Async_Writers)
            then
               declare
                  Position : Dependency_Maps.Cursor;
                  Inserted : Boolean;
                  --  Dummy values required by Hashed_Sets API

               begin
                  --  Try to insert an empty set, do nothing if another value
                  --  is already in the map.
                  M.Insert (Key      => Direct_Mapping_Id (State),
                            Position => Position,
                            Inserted => Inserted);
               end;
            end if;
         end loop;
      end if;

      --  The Initializes contract of a generic package might include generic
      --  actual parameters of mode IN, but they are only visible from within
      --  the instance. When looking from the outside, they must be mapped to
      --  variables referenced in their actual expressions.

      for C in M.Iterate loop
         Map_Generic_In_Formals (Scop, M (C));
      end loop;

      return M;
   end Parse_Initializes;

end Flow_Dependency_Maps;
