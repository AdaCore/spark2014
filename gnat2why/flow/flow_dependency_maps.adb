------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   F L O W _ D E P E N D E N C Y _ M A P S                --
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

with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;

with Treepr; use Treepr;

with Why;

--  with Flow.Debug; use Flow.Debug;

package body Flow_Dependency_Maps is

   use Dependency_Maps;

   function Parse_Raw_Dependency_Map (N : Node_Id)
                                      return Dependency_Maps.Map
     with Pre => Nkind (N) = N_Pragma and then
                 Get_Pragma_Id (Chars (Pragma_Identifier (N))) in
                   Pragma_Depends |
                   Pragma_Refined_Depends |
                   Pragma_Initializes;
   --  Helper function to parse something that looks like a dependency
   --  map; in particular we can parse either a depends or an
   --  initializes aspect.

   ------------------------------
   -- Parse_Raw_Dependency_Map --
   ------------------------------

   function Parse_Raw_Dependency_Map (N : Node_Id)
                                      return Dependency_Maps.Map
   is
      use type Ada.Containers.Count_Type;

      pragma Assert
        (List_Length (Pragma_Argument_Associations (N)) = 1);

      PAA : constant Node_Id :=
        First (Pragma_Argument_Associations (N));
      pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

      M : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;

      Inputs  : Flow_Id_Sets.Set;
      Outputs : Flow_Id_Sets.Set;
   begin
      case Nkind (Expression (PAA)) is
         when N_Null =>
            --  Aspect => null
            return M;

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

         when others =>
            raise Why.Unexpected_Node;
      end case;

      pragma Assert_And_Cut (Nkind (Expression (PAA)) = N_Aggregate);
      --  Aspect => (...)

      --  First we should look at the expressions of the aggregate,
      --  i.e. foo and bar in (foo, bar, baz => ..., bork => ...)
      Row := First (Expressions (Expression (PAA)));
      while Present (Row) loop
         M.Include (Direct_Mapping_Id (Unique_Entity (Entity (Row))),
                    Flow_Id_Sets.Empty_Set);

         Row := Next (Row);
      end loop;

      --  Next, we look at the component associations, i.e. baz and
      --  bork in the above example.
      Row := First (Component_Associations (Expression (PAA)));
      while Present (Row) loop
         Inputs  := Flow_Id_Sets.Empty_Set;
         Outputs := Flow_Id_Sets.Empty_Set;

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

            when N_Identifier | N_Expanded_Name =>
               --  Foo => ...
               pragma Assert (Present (Entity (LHS)));
               Outputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (LHS))));

            when N_Null =>
               --  null => ...
               null;

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
                  pragma Assert (Present (Entity (RHS)));
                  Inputs.Include
                    (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));
                  RHS := Next (RHS);
               end loop;
            when N_Identifier | N_Expanded_Name =>
               pragma Assert (Present (Entity (RHS)));
               Inputs.Include
                 (Direct_Mapping_Id (Unique_Entity (Entity (RHS))));
            when N_Null =>
               null;
            when others =>
               Print_Node_Subtree (RHS);
               raise Why.Unexpected_Node;
         end case;

         --  Assemble map

         if Outputs.Length = 0 and then Inputs.Length >= 1 then
            --  The insert is on purpose - we want this to fail if we
            --  manage to obtain more than one null derives.
            M.Insert (Null_Flow_Id, Flow_Id_Sets.Empty_Set);
            for Input of Inputs loop
               M (Null_Flow_Id).Include (Input);
            end loop;
         else
            for Output of Outputs loop
               M.Include (Output, Flow_Id_Sets.Empty_Set);
               for Input of Inputs loop
                  M (Output).Include (Input);
               end loop;
            end loop;
         end if;

         Row := Next (Row);
      end loop;

      --  Print_Dependency_Map (M);

      return M;
   end Parse_Raw_Dependency_Map;

   -------------------
   -- Parse_Depends --
   -------------------

   function Parse_Depends (N : Node_Id)
                           return Dependency_Maps.Map
   is
   begin
      return Parse_Raw_Dependency_Map (N);
   end Parse_Depends;

   -----------------------
   -- Parse_Initializes --
   -----------------------

   function Parse_Initializes (N : Node_Id)
                               return Dependency_Maps.Map
   is
   begin
      return Parse_Raw_Dependency_Map (N);
   end Parse_Initializes;

end Flow_Dependency_Maps;
