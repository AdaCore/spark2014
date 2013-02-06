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
with Atree; use Atree;
with Sinfo; use Sinfo;
with Nlists; use Nlists;

package body Flow.Control_Flow_Graph is

   use type Flow_Graphs.Vertex_Id;

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
   --  Link all nodes in Froms to the To node in the given graph.

   procedure Linkup
     (CFG   : in out Flow_Graphs.T;
      From  : Flow_Graphs.Vertex_Id;
      To    : Flow_Graphs.Vertex_Id)
      with Pre => From /= Flow_Graphs.Null_Vertex and
                  To   /= Flow_Graphs.Null_Vertex;
   --  Link the From to the To node in the given graph.

   procedure Do_Assignment_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (E) = N_Assignment_Statement;

   procedure Do_Handled_Sequence_Of_Statements
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (E) = N_Handled_Sequence_Of_Statements;

   procedure Do_If_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (E) = N_If_Statement;

   procedure Do_Simple_Return_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (E) = N_Simple_Return_Statement;

   procedure Do_Subprogram_Body
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => Nkind (E) = N_Subprogram_Body;

   procedure Process_Statement_List
     (L  : List_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => List_Length (L) >= 1;

   procedure Process_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
      with Pre => (Nkind (E) in N_Statement_Other_Than_Procedure_Call
                     or Nkind (E) in N_Subprogram_Call);

   --------------
   --  Linkup  --
   --------------

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     Froms : Vertex_Sets.Set;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      for From of Froms loop
         CFG.Add_Edge (From, To);
      end loop;
   end Linkup;

   procedure Linkup (CFG   : in out Flow_Graphs.T;
                     From  : Flow_Graphs.Vertex_Id;
                     To    : Flow_Graphs.Vertex_Id)
   is
   begin
      CFG.Add_Edge (From, To);
   end Linkup;

   -------------------------------
   --  Do_Assignment_Statement  --
   -------------------------------

   procedure Do_Assignment_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  We have a vertex
      FA.CFG.Add_Vertex (E, Null_Attributes, V);

      --  Control goes in V and of V
      CM.Include (Union_Id (E),
                  Graph_Connections'
                    (Standard_Entry => V,
                     Standard_Exits => Vertex_Sets.To_Set (V)));
   end Do_Assignment_Statement;

   -----------------------------------------
   --  Do_Handled_Sequence_Of_Statements  --
   -----------------------------------------

   procedure Do_Handled_Sequence_Of_Statements
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      Stmts : constant List_Id := Statements (E);
   begin
      Process_Statement_List (Stmts, FA, CM);
      --  !!! Workaround
      CM.Include (Union_Id (E), CM.Element (Union_Id (Stmts)));
   end Do_Handled_Sequence_Of_Statements;

   -----------------------
   --  Do_If_Statement  --
   -----------------------

   procedure Do_If_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V         : Flow_Graphs.Vertex_Id;
      If_Part   : constant List_Id := Then_Statements (E);
      Else_Part : constant List_Id := Else_Statements (E);
   begin
      pragma Assert (Elsif_Parts (E) = No_List);

      --  We have a vertex for the if statement itself.
      FA.CFG.Add_Vertex (E, Null_Attributes, V);
      CM.Include (Union_Id (E), No_Connections);
      CM (Union_Id (E)).Standard_Entry := V;

      Process_Statement_List (If_Part, FA, CM);
      Linkup (FA.CFG, V, CM (Union_Id (If_Part)).Standard_Entry);
      CM (Union_Id (E)).Standard_Exits.Union
        (CM (Union_Id (If_Part)).Standard_Exits);

      if Else_Part /= No_List then
         Process_Statement_List (Else_Part, FA, CM);
         Linkup (FA.CFG, V, CM (Union_Id (Else_Part)).Standard_Entry);
         CM (Union_Id (E)).Standard_Exits.Union
           (CM (Union_Id (Else_Part)).Standard_Exits);
      end if;
   end Do_If_Statement;

   ----------------------------------
   --  Do_Simple_Return_Statement  --
   ----------------------------------

   procedure Do_Simple_Return_Statement
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      V : Flow_Graphs.Vertex_Id;
   begin
      --  We need a helper vertex
      FA.CFG.Add_Vertex (E, Null_Attributes, V);
      CM.Include (Union_Id (E), No_Connections);

      --  Control flows in, but there are no standard exits.
      CM (Union_Id (E)).Standard_Entry := V;

      --  Instead we link this node directly to the end node.
      Linkup (FA.CFG, V, FA.End_Vertex);
   end Do_Simple_Return_Statement;

   --------------------------
   --  Do_Subprogram_Body  --
   --------------------------

   procedure Do_Subprogram_Body
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
   begin
      Do_Handled_Sequence_Of_Statements
        (Handled_Statement_Sequence (E), FA, CM);
      CM.Include (Union_Id (E),
                  --  !!! Workaround
                  CM.Element (Union_Id (Handled_Statement_Sequence (E))));
   end Do_Subprogram_Body;

   ------------------------------
   --  Process_Statement_List  --
   ------------------------------

   procedure Process_Statement_List
     (L  : List_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
      P     : Node_Or_Entity_Id;
      Prev  : Node_Or_Entity_Id;
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
               --  This is the first node, so set the standard entry
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
     (E  : Entity_Id;
      FA : in out Flow_Analysis_Graphs;
      CM : in out Connection_Maps.Map)
   is
   begin
      case Nkind (E) is
         when N_Assignment_Statement =>
            Do_Assignment_Statement (E, FA, CM);
         when N_If_Statement =>
            Do_If_Statement (E, FA, CM);
         when N_Simple_Return_Statement =>
            Do_Simple_Return_Statement (E, FA, CM);
         when others =>
            Print_Node_Subtree (E);
            CM.Include (Union_Id (E), No_Connections);
      end case;
   end Process_Statement;

   --------------
   --  Create  --
   --------------

   procedure Create
     (E  : Entity_Id;
      FA : out Flow_Analysis_Graphs)
   is
      Connection_Map : Connection_Maps.Map;
   begin
      --  Start with a blank slate.
      FA := Flow_Analysis_Graphs'
        (Start_Vertex => Flow_Graphs.Null_Vertex,
         End_Vertex   => Flow_Graphs.Null_Vertex,
         NTV          => Node_To_Vertex_Maps.Empty_Map,
         CFG          => Flow_Graphs.Create);
      Connection_Map := Connection_Maps.Empty_Map;

      --  Print the node for debug purposes
      --  Print_Node_Subtree (E);

      --  Create the magic start and end vertices.
      FA.CFG.Add_Vertex (Null_Attributes, FA.Start_Vertex);
      FA.CFG.Add_Vertex (Null_Attributes, FA.End_Vertex);

      --  Produce flowgraph for the body
      Do_Subprogram_Body (E, FA, Connection_Map);

      --  Connect up the start and end nodes.
      Linkup (FA.CFG,
              FA.Start_Vertex,
              Connection_Map (Union_Id (E)).Standard_Entry);
      Linkup (FA.CFG,
              Connection_Map (Union_Id (E)).Standard_Exits,
              FA.End_Vertex);
   end Create;

end Flow.Control_Flow_Graph;
