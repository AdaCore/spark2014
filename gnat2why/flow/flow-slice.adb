------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2015, Altran UK Limited              --
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

with Why;

with Sem_Util;     use Sem_Util;
with Sinfo;        use Sinfo;

with SPARK_Util;   use SPARK_Util;

with Flow_Utility; use Flow_Utility;

package body Flow.Slice is

   use type Node_Sets.Set;
   use type Flow_Id_Sets.Set;
   use type Flow_Graphs.Vertex_Id;

   ----------------------------------------------------------------------
   --  Local procedures for local subprograms
   ----------------------------------------------------------------------

   function Internal_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id;
      IPFA    : Boolean)
      return Vertex_Sets.Set;
   --  Helper function to compute the dependencies for a single
   --  vertex.

   -------------------------
   -- Internal_Dependency --
   -------------------------

   function Internal_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id;
      IPFA    : Boolean)
      return Vertex_Sets.Set
   is
      Deps : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Visitor
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  If the visited vertex is an in vertex or a procedure
      --  parameter vertex, we add it to the set of things we depend
      --  on.

      procedure Visitor
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         F : constant Flow_Id := FA.PDG.Get_Key (V);
      begin
         case F.Variant is
            when Initial_Value | Final_Value =>
               Deps.Include (V);
            when In_View | Out_View =>
               if IPFA then
                  Deps.Include (V);
               end if;
            when Initial_Grouping | Final_Grouping =>
               null;
            when Normal_Use =>
               null;
         end case;
         TV := Flow_Graphs.Continue;
      end Visitor;

   begin
      Flow_Graphs.DFS (G             => FA.PDG,
                       Start         => V_Final,
                       Include_Start => False,
                       Visitor       => Visitor'Access,
                       Reversed      => True);
      return Deps;
   end Internal_Dependency;

   ----------------------------------------------------------------------
   --  Package subprograms
   ----------------------------------------------------------------------

   ----------------
   -- Dependency --
   ----------------

   function Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Flow_Id_Sets.Set
   is
      Tmp  : constant Vertex_Sets.Set :=
        Internal_Dependency (FA      => FA,
                             V_Final => V_Final,
                             IPFA    => False);

      Deps : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for V of Tmp loop
         Deps.Include (Change_Variant (FA.PDG.Get_Key (V), Normal_Use));
      end loop;
      return Deps;
   end Dependency;

   ---------------------
   -- IPFA_Dependency --
   ---------------------

   function IPFA_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Vertex_Sets.Set
   is
   begin
      return Internal_Dependency (FA      => FA,
                                  V_Final => V_Final,
                                  IPFA    => True);
   end IPFA_Dependency;

   ---------------------------------
   -- Compute_Dependency_Relation --
   ---------------------------------

   function Compute_Dependency_Relation
     (FA : Flow_Analysis_Graphs)
      return Dependency_Maps.Map
   is

      function Flow_Equivalent (F : Flow_Id) return Flow_Id
        with Post => Flow_Equivalent'Result.Variant = Normal_Use;
      --  Given a flow id, return the view the dependency relation
      --  cares about.

      function Flow_Equivalent (F : Flow_Id) return Flow_Id
      is
      begin
         case F.Kind is
            when Direct_Mapping        |
                 Magic_String          |
                 Synthetic_Null_Export |
                 Record_Field          =>
               return Change_Variant (Entire_Variable (F), Normal_Use);

            when Null_Value =>
               raise Why.Unexpected_Node;
         end case;
      end Flow_Equivalent;

      In_Vertices   : Vertex_Sets.Set     := Vertex_Sets.Empty_Set;
      Out_Vertices  : Vertex_Sets.Set     := Vertex_Sets.Empty_Set;

      Unused_Inputs : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;

      Out_Discrim   : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;
      --  We need to keep track of discriminated or unconstrained out
      --  parameters, as the implicit input (the discriminant) is
      --  never unused. So if it is unused after all we silently take
      --  it out the unused_inputs set, so that we don't produce a
      --  flow error about a missing null dependency.

      DM            : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      use type Vertex_Sets.Set;

   begin

      --  Determine all out vertices.

      for V_Final of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : constant Flow_Id      := FA.PDG.Get_Key (V_Final);
            Attr    : constant V_Attributes := FA.Atr (V_Final);
         begin
            if F_Final.Variant = Final_Value
              and Attr.Is_Export
              and not Synthetic (F_Final)
            then
               Out_Vertices.Include (V_Final);
            end if;
         end;
      end loop;

      --  Determine all input vertices.

      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Initial : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Attr      : constant V_Attributes := FA.Atr (V_Initial);
         begin
            if F_Initial.Variant = Initial_Value
              and Attr.Is_Import
              and not Synthetic (F_Initial)
            then
               In_Vertices.Include (V_Initial);
               Unused_Inputs.Include (Flow_Equivalent (F_Initial));

               if (Is_Discriminant (F_Initial) or Is_Bound (F_Initial))
                 and then Attr.Mode = Mode_Out
               then
                  --  See above about suppressing "null => foo"
                  --  dependency error messages for out parameters and
                  --  globals.
                  Out_Discrim.Include
                    (Change_Variant (Entire_Variable (F_Initial),
                                     Normal_Use));
               end if;
            end if;
         end;
      end loop;

      --  Determine dependencies.

      for V_Out of Out_Vertices loop
         declare
            F_In  : Flow_Id;
            F_Out : constant Flow_Id :=
              Flow_Equivalent (FA.PDG.Get_Key (V_Out));

            --  Compute dependencies (and filter out local variables).
            Deps : constant Vertex_Sets.Set :=
              Internal_Dependency (FA      => FA,
                                   V_Final => V_Out,
                                   IPFA    => False)
              and In_Vertices;
         begin
            if not DM.Contains (F_Out) then
               DM.Include (F_Out, Flow_Id_Sets.Empty_Set);
            end if;

            for V_In of Deps loop
               F_In := Flow_Equivalent (FA.PDG.Get_Key (V_In));

               DM (F_Out).Include (F_In);
               Unused_Inputs.Exclude (F_In);
            end loop;
         end;
      end loop;

      DM.Include (Null_Flow_Id, Unused_Inputs - Out_Discrim);

      return DM;

   end Compute_Dependency_Relation;

   ---------------------
   -- Compute_Globals --
   ---------------------

   procedure Compute_Globals
     (FA                : Flow_Analysis_Graphs;
      Inputs_Proof      : out Node_Sets.Set;
      Inputs            : out Node_Sets.Set;
      Outputs           : out Node_Sets.Set;
      Proof_Calls       : out Node_Sets.Set;
      Definite_Calls    : out Node_Sets.Set;
      Conditional_Calls : out Node_Sets.Set;
      Local_Variables   : out Node_Sets.Set)
   is
      --  The "Get" functions that follow return sets of nodes that
      --  are purely of the mode described in their names. This is
      --  pointed out so as to prevent confusion between the functions
      --  and the formal parameters of Compute_Globals (where an Input
      --  could also appear as an Output).

      function Get_Inputs_Or_Proof_Ins return Node_Sets.Set;
      --  Returns all Globals that are purely of mode Input or Proof_In

      function Get_Outputs return Node_Sets.Set;
      --  Returns all Globals that are purely of mode Output

      function Get_In_Outs return Node_Sets.Set;
      --  Returns all Globals that are of mode In_Out

      function Get_Proof_Ins return Node_Sets.Set;
      --  Returns all Globals that are of mode Proof_In

      --  The functions that follow facilitate calculation of
      --  subprogram calls.

      function Get_Proof_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are only ever called in proof
      --  related vertices.

      function Get_Definite_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are definitely called

      function Get_Local_Variables return Node_Sets.Set;
      --  Traverses the tree under FA.Analyzed_Entity and gathers all
      --  object declared.

      function Subprograms_Without_Contracts
        (NS : Node_Sets.Set)
         return Node_Sets.Set;
      --  Returns a subset of NS that comprises those subprograms that
      --  have no user-provided Global or Depends contracts.

      -----------------------------
      -- Get_Inputs_Or_Proof_Ins --
      -----------------------------

      function Get_Inputs_Or_Proof_Ins return Node_Sets.Set is
         All_Ins   : Node_Sets.Set := Node_Sets.Empty_Set;
         FS        : Flow_Id_Sets.Set;
         V_Initial : Flow_Graphs.Vertex_Id;
         V_Final   : Flow_Graphs.Vertex_Id;
         Guilty    : Boolean;
      begin
         for G of FA.GG.Globals loop
            --  We go through all Globals and check if their
            --  corresponding 'Final vertex has a single in neighbour
            --  that is the 'Initial vertex.

            Guilty := False;  --  Innocent till found guilty

            FS := Flatten_Variable (Direct_Mapping_Id (G), FA.B_Scope);

            for Comp of FS loop
               V_Initial := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Initial_Value));

               V_Final   := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Final_Value));

               if not (FA.PDG.In_Neighbour_Count (V_Final) = 1
                         and then (for some V of FA.PDG.Get_Collection
                                     (V_Final,
                                      Flow_Graphs.In_Neighbours) =>
                                        V = V_Initial))
               then
                  Guilty := True;
                  exit;
               end if;
            end loop;

            if not Guilty then
               All_Ins.Insert (G);
            end if;
         end loop;

         return All_Ins;
      end Get_Inputs_Or_Proof_Ins;

      -----------------
      -- Get_Outputs --
      -----------------

      function Get_Outputs return Node_Sets.Set is
         All_Outs  : Node_Sets.Set := Node_Sets.Empty_Set;
         FS        : Flow_Id_Sets.Set;
         V_Initial : Flow_Graphs.Vertex_Id;
         Guilty    : Boolean;
      begin
         for G of FA.GG.Globals loop
            --  We go through all Globals and check if their
            --  corresponding 'Initial vertex has no Out_Neighbours.

            Guilty := False;  --  Innocent till found guilty

            FS := Flatten_Variable (Direct_Mapping_Id (G), FA.B_Scope);

            for Comp of FS loop
               V_Initial := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Initial_Value));

               if not (FA.PDG.Out_Neighbour_Count (V_Initial) = 0) then
                  Guilty := True;
                  exit;
               end if;
            end loop;

            if not Guilty then
               All_Outs.Insert (G);
            end if;
         end loop;

         return All_Outs;
      end Get_Outputs;

      -----------------
      -- Get_In_Outs --
      -----------------

      function Get_In_Outs return Node_Sets.Set is
      begin
         --  The Globals that are of mode In_Out can be computed
         --  by subtracting from the set of all Globals the sets that
         --  are purely of modes Input, Proof_In and Output.

         return FA.GG.Globals - Get_Inputs_Or_Proof_Ins - Get_Outputs;
      end Get_In_Outs;

      -------------------
      -- Get_Proof_Ins --
      -------------------

      function Get_Proof_Ins return Node_Sets.Set is
         All_Proof_Ins : Node_Sets.Set := Get_Inputs_Or_Proof_Ins;

         A             : V_Attributes;
      begin
         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            --  We go through all vertices in the graph and we
            --  subtract from the All_Proof_Ins set the variables that
            --  are used on vertices that are not related to proof.

            A := FA.Atr.Element (V);

            if FA.PDG.Get_Key (V).Variant /= Final_Value
              and then not A.Is_Proof
            then
               All_Proof_Ins := All_Proof_Ins -
                 To_Node_Set (To_Entire_Variables (A.Variables_Used));
            end if;
         end loop;

         return All_Proof_Ins;
      end Get_Proof_Ins;

      ---------------------------
      -- Get_Proof_Subprograms --
      ---------------------------

      function Get_Proof_Subprograms return Node_Sets.Set is
         All_Proof_Subprograms : Node_Sets.Set := FA.Direct_Calls;
         A                     : V_Attributes;
      begin
         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            --  We go through all vertices in the graph and we
            --  subtract from the All_Proof_Subprograms set the
            --  subprograms that are called on vertices that are not
            --  related to proof.

            A := FA.Atr.Element (V);

            if not A.Is_Proof then
               All_Proof_Subprograms := All_Proof_Subprograms -
                                          A.Subprograms_Called;
            end if;
         end loop;

         return Subprograms_Without_Contracts (All_Proof_Subprograms);
      end Get_Proof_Subprograms;

      ------------------------------
      -- Get_Definite_Subprograms --
      ------------------------------

      function Get_Definite_Subprograms return Node_Sets.Set is
         All_Definite_Subprograms  : Node_Sets.Set := Node_Sets.Empty_Set;
         F                         : Flow_Id;
         V_Initial                 : Flow_Graphs.Vertex_Id;
      begin
         for G of FA.Direct_Calls loop
            --  We go through all Subprograms and check if their
            --  corresponding 'Initial vertex has no Out_Neighbours.

            F := Direct_Mapping_Id (G);
            V_Initial := FA.PDG.Get_Vertex (Change_Variant (F, Initial_Value));

            if FA.PDG.Out_Neighbour_Count (V_Initial) = 0 then
               All_Definite_Subprograms.Include (G);
            end if;
         end loop;

         return Subprograms_Without_Contracts (All_Definite_Subprograms);
      end Get_Definite_Subprograms;

      -------------------------
      -- Get_Local_Variables --
      -------------------------

      function Get_Local_Variables return Node_Sets.Set is
         NS : Node_Sets.Set := Node_Sets.Empty_Set;

         function Get_Object_Declaration (N : Node_Id) return Traverse_Result;
         --  Picks up an object coming from an object declaration.

         procedure Gather_Local_Variables is
            new Traverse_Proc (Get_Object_Declaration);

         ----------------------------
         -- Get_Object_Declaration --
         ----------------------------

         function Get_Object_Declaration (N : Node_Id) return Traverse_Result
         is
         begin
            if Nkind (N) = N_Object_Declaration then
               if Present (Full_View (Defining_Entity (N))) then
                  NS.Include (Full_View (Defining_Entity (N)));
               else
                  NS.Include (Defining_Entity (N));
               end if;
            end if;

            return OK;
         end Get_Object_Declaration;

      begin
         --  Gather formal parameters of the subprogram itself.
         declare
            E : Entity_Id;
         begin
            E := First_Formal (FA.Analyzed_Entity);

            while Present (E) loop
               if Present (Full_View (E)) then
                  NS.Include (Full_View (E));
               else
                  NS.Include (E);
               end if;
               Next_Formal (E);
            end loop;
         end;

         Gather_Local_Variables
           (SPARK_Util.Get_Subprogram_Body (FA.Analyzed_Entity));

         return NS;
      end Get_Local_Variables;

      -----------------------------------
      -- Subprograms_Without_Contracts --
      -----------------------------------

      function Subprograms_Without_Contracts
        (NS : Node_Sets.Set)
         return Node_Sets.Set
      is
         Subs_Without_Contracts : Node_Sets.Set := Node_Sets.Empty_Set;
      begin
         for N of NS loop
            if Rely_On_Generated_Global (N, FA.B_Scope)
              or else not Has_User_Supplied_Globals (N)
            then
               Subs_Without_Contracts.Include (N);
            end if;
         end loop;

         return Subs_Without_Contracts;
      end Subprograms_Without_Contracts;

   --  Beginning of Compute_Globals

   begin
      Inputs_Proof      := Get_Proof_Ins;
      Inputs            := Get_In_Outs or (Get_Inputs_Or_Proof_Ins -
                                             Get_Proof_Ins);
      Outputs           := Get_In_Outs or Get_Outputs;
      Proof_Calls       := Get_Proof_Subprograms;
      Definite_Calls    := Get_Definite_Subprograms - Proof_Calls;
      Conditional_Calls := Subprograms_Without_Contracts
        (FA.Direct_Calls - Definite_Calls - Proof_Calls);
      Local_Variables   := Get_Local_Variables;
   end Compute_Globals;

end Flow.Slice;
