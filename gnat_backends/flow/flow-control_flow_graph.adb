------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              F L O W . C O N T R O L _ F L O W _ G R A P H               --
--                                                                          --
--                                 S p e c                                  --
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

with Treepr; use Treepr;
with Atree;  use Atree;
with Sinfo;  use Sinfo;
with Einfo;  use Einfo;
with Nlists; use Nlists;

with Flow.Debug; use Flow.Debug;
pragma Unreferenced (Flow.Debug);

with Why;

package body Flow.Control_Flow_Graph is

   use type Flow_Graphs.Vertex_Id;
   use type Ada.Containers.Count_Type;

   use Vertex_Sets;

   type Graph_Connections is record
      Standard_Entry : Flow_Graphs.Vertex_Id;
      Standard_Exits : Vertex_Sets.Set;
   end record;

   No_Connections : constant Graph_Connections :=
     Graph_Connections'(Standard_Entry => Flow_Graphs.Null_Vertex,
                        Standard_Exits => Vertex_Sets.Empty_Set);

   function Union_Hash (X : Union_Id) return Ada.Containers.Hash_Type
   is (Ada.Containers.Hash_Type (abs (X)));

   package Connection_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Union_Id,
      Element_Type    => Graph_Connections,
      Hash            => Union_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   procedure Linkup
     (CFG   : in out Flow_Graphs.T;
      Froms : Vertex_Sets.Set;
      To    : Flow_Graphs.Vertex_Id)
      with Pre => To /= Flow_Graphs.Null_Vertex;
   --  Link all vertices in Froms to the To vertex in the given graph.

   procedure Linkup
     (CFG   : in out Flow_Graphs.T;
      From  : Flow_Graphs.Vertex_Id;
      To    : Flow_Graphs.Vertex_Id)
      with Pre => From /= Flow_Graphs.Null_Vertex and
                  To   /= Flow_Graphs.Null_Vertex;
   --  Link the From to the To vertex in the given graph.

   function Get_Variable_Set (N : Node_Id) return Flow_Id_Sets.Set;
   --  Obtain all variables (which may include types) used in an
   --  expression.

   function Get_Variable_Set (L : List_Id) return Flow_Id_Sets.Set;
   --  As above, but operating on a list.

   procedure Do_Assignment_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Assignment_Statement;

   procedure Do_Exit_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Exit_Statement;

   procedure Do_Handled_Sequence_Of_Statements
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Handled_Sequence_Of_Statements;

   procedure Do_If_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_If_Statement;

   procedure Do_Loop_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Loop_Statement;

   procedure Do_Simple_Return_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Simple_Return_Statement;

   procedure Do_Subprogram_Body
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (N) = N_Subprogram_Body;

   procedure Process_Statement_List
     (L  : List_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => List_Length (L) >= 1;

   procedure Process_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => (Nkind (N) in N_Statement_Other_Than_Procedure_Call
                     or Nkind (N) in N_Subprogram_Call);

   procedure Simplify
     (G : in out Flow_Graphs.T'Class);
   --  Remove all null vertices from the graph.

   --------------
   --  Linkup  --
   --------------

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     Froms : Vertex_Sets.Set;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      for From of Froms loop
         CFG.Add_Edge (From, To, EC_Default);
      end loop;
   end Linkup;

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     From  : Flow_Graphs.Vertex_Id;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      CFG.Add_Edge (From, To, EC_Default);
   end Linkup;

   ------------------------
   --  Get_Variable_Set  --
   ------------------------

   function Get_Variable_Set (N : Node_Id) return Flow_Id_Sets.Set
   is
      VS     : Flow_Id_Sets.Set;
      Unused : Traverse_Final_Result;
      pragma Unreferenced (Unused);

      function Proc (N : Node_Id) return Traverse_Result;

      function Proc (N : Node_Id) return Traverse_Result
      is
      begin
         case Nkind (N) is
            when N_Identifier =>
               if Entity (N) /= Empty then
                  case Ekind (Entity (N)) is
                     when E_Variable |
                       E_Loop_Parameter |
                       E_Out_Parameter |
                       E_In_Parameter |
                       E_In_Out_Parameter |
                       E_Constant =>
                        VS.Include (Direct_Mapping_Id (Entity (N)));
                     when others =>
                        null;
                  end case;
               end if;
            when others =>
               null;
         end case;
         return OK;
      end Proc;

      function Traverse is new Traverse_Func (Process => Proc);
   begin
      Unused := Traverse (N);
      return VS;
   end Get_Variable_Set;

   function Get_Variable_Set (L : List_Id) return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;
      P  : Node_Id;
   begin
      P := First (L);
      while P /= Empty loop
         VS.Union (Get_Variable_Set (P));

         P := Next (P);
      end loop;
      return VS;
   end Get_Variable_Set;

   -------------------------------
   --  Do_Assignment_Statement  --
   -------------------------------

   procedure Do_Assignment_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      use type Flow_Id_Sets.Set;

      V : Flow_Graphs.Vertex_Id;

      V_Used_RHS  : Flow_Id_Sets.Set;
      --  Things used because they appear on the RHS

      V_Used_LHS  : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things used because they appear on the LHS (in A (J), J
      --  would be used).

      V_Def_LHS   : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things defined because they appear on the LHS (in A (J), A
      --  would be used).

      V_Also_Used : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      --  Things used because of the limitations of flow analysis. In
      --  (A (J) := 0, A would also be used as the other elements do
      --  not change.)
   begin
      --  Work out which variables we use and define.
      V_Used_RHS := Get_Variable_Set (Expression (N));

      declare
         LHS : Node_Id renames Name (N);
      begin
         case Nkind (LHS) is
            when N_Identifier =>
               --  X :=
               V_Def_LHS := Get_Variable_Set (LHS);
            when N_Selected_Component =>
               --  R.A :=
               V_Def_LHS := Get_Variable_Set (Prefix (LHS));
               V_Also_Used := V_Def_LHS;
            when N_Indexed_Component =>
               --  R.A (...) :=
               V_Def_LHS  := Get_Variable_Set (Prefix (LHS));
               V_Used_LHS := Get_Variable_Set (Expressions (LHS));
               V_Also_Used := V_Def_LHS;
            when others =>
               raise Why.Not_Implemented;
         end case;
      end;

      --  Print the node and its def-use effect
      --  Print_Node_Subtree (N);
      --  Print_Node_Set (V_Def_LHS);
      --  Print_Node_Set (V_Used_LHS or V_Used_RHS or V_Also_Used);

      pragma Assert (V_Def_LHS.Length = 1);

      --  We have a vertex
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         V_Attributes'(Is_Null_Node      => False,
                       Is_Program_Node   => True,
                       Is_Initialised    => False,
                       Is_Export         => False,
                       Variables_Defined => V_Def_LHS,
                       Variables_Used    => V_Used_RHS
                         or V_Used_LHS
                         or V_Also_Used),
         V);

      --  Control goes in V and of V
      CM.Include (Union_Id (N),
                  Graph_Connections'
                    (Standard_Entry => V,
                     Standard_Exits => Vertex_Sets.To_Set (V)));
   end Do_Assignment_Statement;

   -------------------------
   --  Do_Exit_Statement  --
   -------------------------

   procedure Do_Exit_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
      L : Node_Id := N;
   begin
      --  Go up the tree until we find the loop we are exiting from.
      if Name (N) = Empty then
         --  We just need to find the enclosing loop.
         loop
            L := Parent (L);
            exit when Nkind (L) = N_Loop_Statement;
         end loop;
      else
         --  We have a named loop, which we need to find.
         loop
            L := Parent (L);
            exit when Nkind (L) = N_Loop_Statement and then
              Entity (Identifier (L)) = Entity (Name (N));
         end loop;
      end if;

      --  Conditional and unconditional exits are different. One
      --  requires an extra vertex, the other does not.
      if Condition (N) = Empty then
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Null_Node_Attributes,
                            V);
         CM.Include (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry => V,
                        Standard_Exits => Vertex_Sets.Empty_Set));

         CM (Union_Id (L)).Standard_Exits.Include (V);

      else
         FA.CFG.Add_Vertex
           (Direct_Mapping_Id (N),
            V_Attributes'(Is_Null_Node      => False,
                          Is_Program_Node   => True,
                          Is_Initialised    => False,
                          Is_Export         => False,
                          Variables_Defined => Flow_Id_Sets.Empty_Set,
                          Variables_Used    => Get_Variable_Set
                            (Condition (N))),
            V);
         CM.Include (Union_Id (N),
                     Graph_Connections'
                       (Standard_Entry => V,
                        Standard_Exits => Vertex_Sets.To_Set (V)));

         CM (Union_Id (L)).Standard_Exits.Include (V);
      end if;
   end Do_Exit_Statement;

   -----------------------------------------
   --  Do_Handled_Sequence_Of_Statements  --
   -----------------------------------------

   procedure Do_Handled_Sequence_Of_Statements
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      Stmts : constant List_Id := Statements (N);
   begin
      Process_Statement_List (Stmts, FA, CM);
      --  !!! Workaround
      CM.Include (Union_Id (N), CM.Element (Union_Id (Stmts)));
   end Do_Handled_Sequence_Of_Statements;

   -----------------------
   --  Do_If_Statement  --
   -----------------------

   procedure Do_If_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V         : Flow_Graphs.Vertex_Id;
      If_Part   : constant List_Id := Then_Statements (N);
      Else_Part : constant List_Id := Else_Statements (N);
   begin
      pragma Assert (Elsif_Parts (N) = No_List);

      --  We have a vertex for the if statement itself.
      FA.CFG.Add_Vertex
        (Direct_Mapping_Id (N),
         V_Attributes'(Is_Null_Node      => False,
                       Is_Program_Node   => True,
                       Is_Initialised    => False,
                       Is_Export         => False,
                       Variables_Defined => Flow_Id_Sets.Empty_Set,
                       Variables_Used    => Get_Variable_Set (Condition (N))),
         V);
      CM.Include (Union_Id (N), No_Connections);
      CM (Union_Id (N)).Standard_Entry := V;

      Process_Statement_List (If_Part, FA, CM);
      Linkup (FA.CFG, V, CM (Union_Id (If_Part)).Standard_Entry);
      CM (Union_Id (N)).Standard_Exits.Union
        (CM (Union_Id (If_Part)).Standard_Exits);

      if Else_Part /= No_List then
         Process_Statement_List (Else_Part, FA, CM);
         Linkup (FA.CFG, V, CM (Union_Id (Else_Part)).Standard_Entry);
         CM (Union_Id (N)).Standard_Exits.Union
           (CM (Union_Id (Else_Part)).Standard_Exits);
      else
         CM (Union_Id (N)).Standard_Exits.Insert (V);
      end if;

   end Do_If_Statement;

   -------------------------
   --  Do_Loop_Statement  --
   -------------------------

   procedure Do_Loop_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  Start with a blank slate for the loops entry and exit.
      CM.Include (Union_Id (N), No_Connections);

      --  Construct graph for the loop body. Please note that early
      --  exists may alrady change the above, so be sure to only use
      --  union or include, instead of setting the standard exits.
      Process_Statement_List (Statements (N), FA, CM);

      if Iteration_Scheme (N) = Empty then
         --  We have a loop.

         --  We have a null vertex for the loop, as we have no
         --  condition.
         FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                            Null_Node_Attributes,
                            V);

         --  Entry point for the loop is V.
         CM (Union_Id (N)).Standard_Entry := V;

         --  Exit from the loop is at the end of the loop, i.e. we are
         --  always going round at least once.
         --  !!! workaround
         CM (Union_Id (N)).Standard_Exits.Union
           (CM.Element (Union_Id (Statements (N))).Standard_Exits);

      else
         --  We have either a while loop or a for loop.

         --  We have a vertex for the loop condition, depending on its
         --  iteration scheme.
         if Condition (Iteration_Scheme (N)) /= Empty then
            --  We have a while loop.

            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               V_Attributes'
                 (Is_Null_Node      => False,
                  Is_Program_Node   => True,
                  Is_Initialised    => False,
                  Is_Export         => False,
                  Variables_Defined => Flow_Id_Sets.Empty_Set,
                  Variables_Used    => Get_Variable_Set
                    (Condition (Iteration_Scheme (N)))),
               V);
         else
            --  We have a for loop.
            pragma Assert (Loop_Parameter_Specification (Iteration_Scheme (N))
                             /= Empty);

            FA.CFG.Add_Vertex
              (Direct_Mapping_Id (N),
               V_Attributes'
                 (Is_Null_Node      => False,
                  Is_Program_Node   => True,
                  Is_Initialised    => False,
                  Is_Export         => False,
                  Variables_Defined => Flow_Id_Sets.To_Set
                    (Direct_Mapping_Id (Defining_Identifier
                                          (Loop_Parameter_Specification
                                             (Iteration_Scheme (N))))),
                  Variables_Used    => Get_Variable_Set
                    (Discrete_Subtype_Definition (Loop_Parameter_Specification
                                                    (Iteration_Scheme (N))))),
               V);
         end if;

         --  Flow for the loops with iteration schemes goes into the
         --  condition and then out again.
         CM (Union_Id (N)).Standard_Entry := V;
         CM (Union_Id (N)).Standard_Exits.Include (V);
      end if;

      --  Loop the loop: V -> body -> V
      Linkup (FA.CFG, V, CM (Union_Id (Statements (N))).Standard_Entry);
      Linkup (FA.CFG, CM (Union_Id (Statements (N))).Standard_Exits, V);
   end Do_Loop_Statement;

   ----------------------------------
   --  Do_Simple_Return_Statement  --
   ----------------------------------

   procedure Do_Simple_Return_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  We need a helper vertex
      FA.CFG.Add_Vertex (Direct_Mapping_Id (N),
                         Null_Node_Attributes,
                         V);
      CM.Include (Union_Id (N), No_Connections);

      --  Control flows in, but there are no standard exits.
      CM (Union_Id (N)).Standard_Entry := V;

      --  Instead we link this vertex directly to the end vertex.
      Linkup (FA.CFG, V, FA.End_Vertex);
   end Do_Simple_Return_Statement;

   --------------------------
   --  Do_Subprogram_Body  --
   --------------------------

   procedure Do_Subprogram_Body
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
   begin
      Do_Handled_Sequence_Of_Statements
        (Handled_Statement_Sequence (N), FA, CM);
      CM.Include (Union_Id (N),
                  --  !!! Workaround
                  CM.Element (Union_Id (Handled_Statement_Sequence (N))));
   end Do_Subprogram_Body;

   ------------------------------
   --  Process_Statement_List  --
   ------------------------------

   procedure Process_Statement_List
     (L  : List_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      P    : Node_Or_Entity_Id;
      Prev : Node_Or_Entity_Id;
   begin
      if List_Length (L) = 1 then
         Process_Statement (First (L), FA, CM);
         --  !!! Workaround, to be reproduced later
         CM.Include (Union_Id (L), CM.Element (Union_Id (First (L))));
      else
         --  We need a connection map for this sequence.
         CM.Include (Union_Id (L), No_Connections);

         --  Create initial nodes for the statements.
         P    := First (L);
         Prev := Empty;
         while P /= Empty loop
            Process_Statement (P, FA, CM);

            --  Connect this statement to the previous one.
            if Prev /= Empty then
               Linkup (FA.CFG,
                       CM (Union_Id (Prev)).Standard_Exits,
                       CM (Union_Id (P)).Standard_Entry);
            else
               --  This is the first vertex, so set the standard entry
               --  of the list.
               CM (Union_Id (L)).Standard_Entry :=
                 CM (Union_Id (P)).Standard_Entry;
            end if;

            --  Go to the next statement
            Prev := P;
            P    := Next (P);
         end loop;

         --  Finally, set the standard exits of the list.
         CM (Union_Id (L)).Standard_Exits :=
           CM (Union_Id (Prev)).Standard_Exits;
      end if;
   end Process_Statement_List;

   -------------------------
   --  Process_Statement  --
   -------------------------

   procedure Process_Statement
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
   begin
      case Nkind (N) is
         when N_Assignment_Statement =>
            Do_Assignment_Statement (N, FA, CM);
         when N_Exit_Statement =>
            Do_Exit_Statement (N, FA, CM);
         when N_If_Statement =>
            Do_If_Statement (N, FA, CM);
         when N_Loop_Statement =>
            Do_Loop_Statement (N, FA, CM);
         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (N, FA, CM);
         when others =>
            Print_Node_Subtree (N);
            CM.Include (Union_Id (N), No_Connections);
            raise Why.Not_Implemented;
      end case;
   end Process_Statement;

   ----------------
   --  Simplify  --
   ----------------

   procedure Simplify
     (G : in out Flow_Graphs.T'Class)
   is
      A : V_Attributes;
   begin
      for V of G.Get_Collection (Flow_Graphs.All_Vertices) loop
         if G.Get_Attributes (V).Is_Null_Node then
            --  Close the subgraph indicated by V's neighbours.
            for A of G.Get_Collection (V, Flow_Graphs.In_Neighbours) loop
               for B of G.Get_Collection (V, Flow_Graphs.Out_Neighbours) loop
                  G.Add_Edge (A, B, EC_Default);
               end loop;
            end loop;

            --  Remove all edges from the vertex.
            G.Clear_Vertex (V);

            --  Clear the Is_Program_Node flag.
            A := G.Get_Attributes (V);
            A.Is_Program_Node := False;
            G.Set_Attributes (V, A);
         end if;
      end loop;
   end Simplify;

   --------------
   --  Create  --
   --------------

   procedure Create
     (N  : Node_Id;
      FA : in out Flow_Analysis_Graphs)
   is
      Connection_Map : Connection_Maps.Map;
   begin
      --  Start with a blank slate.
      Connection_Map := Connection_Maps.Empty_Map;

      --  Print the node for debug purposes
      --  Print_Node_Subtree (N);

      --  Create the magic start and end vertices.
      FA.CFG.Add_Vertex (Null_Attributes, FA.Start_Vertex);
      FA.CFG.Add_Vertex (Null_Attributes, FA.End_Vertex);

      --  Produce flowgraph for the body
      Do_Subprogram_Body (N, FA, Connection_Map);

      --  Work out all variables and add 'initial and 'final vertices.
      FA.Vars := Get_Variable_Set (N);
      for F of FA.Vars loop
         case F.Kind is
            when Direct_Mapping =>
               declare
                  N : constant Node_Id := Get_Direct_Mapping_Id (F);
                  V : Flow_Graphs.Vertex_Id;
                  Is_Initialised : Boolean;
                  Is_Export      : Boolean;
               begin
                  --  Setup the n'initial vertex. Note that
                  --  initialisation for variables is detected (and
                  --  set) when building the flow graph for
                  --  declarative parts.
                  case Ekind (N) is
                     when E_In_Out_Parameter |
                       E_In_Parameter =>
                        Is_Initialised := True;
                     when others =>
                        Is_Initialised := False;
                  end case;

                  FA.CFG.Add_Vertex
                    (Direct_Mapping_Id (N, Initial_Value),
                     V_Attributes'
                       (Is_Null_Node      => False,
                        Is_Program_Node   => False,
                        Is_Initialised    => Is_Initialised,
                        Is_Export         => False,
                        Variables_Defined => Flow_Id_Sets.To_Set (F),
                        Variables_Used    => Flow_Id_Sets.Empty_Set),
                     V);
                  Linkup (FA.CFG, V, FA.Start_Vertex);

                  --  Setup the n'final vertex. TODO: global out
                  --  variables are also exports.
                  case Ekind (N) is
                     when E_In_Out_Parameter |
                       E_Out_Parameter =>
                        Is_Export := True;
                     when others =>
                        Is_Export := False;
                  end case;

                  FA.CFG.Add_Vertex
                    (Direct_Mapping_Id (N, Final_Value),
                     V_Attributes'
                       (Is_Null_Node      => False,
                        Is_Program_Node   => False,
                        Is_Initialised    => False,
                        Is_Export         => Is_Export,
                        Variables_Defined => Flow_Id_Sets.Empty_Set,
                        Variables_Used    => Flow_Id_Sets.To_Set (F)),
                     V);
                  Linkup (FA.CFG, FA.End_Vertex, V);
               end;
            when others =>
               raise Why.Not_Implemented;
         end case;
      end loop;
      --  Print_Node_Set (FA.Vars);

      --  Connect up the start and end vertices.
      Linkup (FA.CFG,
              FA.Start_Vertex,
              Connection_Map (Union_Id (N)).Standard_Entry);
      Linkup (FA.CFG,
              Connection_Map (Union_Id (N)).Standard_Exits,
              FA.End_Vertex);

      --  Simplify graph by removing all null vertices.
      Simplify (FA.CFG);
   end Create;

end Flow.Control_Flow_Graph;
