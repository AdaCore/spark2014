------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
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

with Flow_Utility;     use Flow_Utility;
with Nlists;           use Nlists;
with Sem_Aux;          use Sem_Aux;
with Sem_Type;         use Sem_Type;
with Sem_Util;         use Sem_Util;
with Sinfo;            use Sinfo;
with Snames;           use Snames;
with SPARK_Definition; use SPARK_Definition;
with SPARK_Util;       use SPARK_Util;
with Why;

package body Flow.Slice is

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

      ---------------------
      -- Flow_Equivalent --
      ---------------------

      function Flow_Equivalent (F : Flow_Id) return Flow_Id is
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

   --  Start of processing for Compute_Dependency_Relation

   begin

      --  Determine all out vertices.

      for V_Final of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : constant Flow_Id      := FA.PDG.Get_Key (V_Final);
         begin
            if F_Final.Variant = Final_Value
              and FA.Atr (V_Final).Is_Export
              and not Synthetic (F_Final)
            then
               Out_Vertices.Include (V_Final);
            end if;
         end;
      end loop;

      --  Determine all input vertices.

      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            use Attribute_Maps;
            F_Initial : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Attr      : constant Constant_Reference_Type := FA.Atr (V_Initial);
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
     (FA                    : Flow_Analysis_Graphs;
      Inputs_Proof          : out Node_Sets.Set;
      Inputs                : out Node_Sets.Set;
      Outputs               : out Node_Sets.Set;
      Proof_Calls           : out Node_Sets.Set;
      Definite_Calls        : out Node_Sets.Set;
      Conditional_Calls     : out Node_Sets.Set;
      Local_Variables       : out Node_Sets.Set;
      Local_Subprograms     : out Node_Sets.Set;
      Local_Definite_Writes : out Node_Sets.Set)
   is
      --  The "Get" functions that follow return sets of nodes that
      --  are purely of the mode described in their names. This is
      --  pointed out so as to prevent confusion between the functions
      --  and the formal parameters of Compute_Globals (where an Input
      --  could also appear as an Output).

      function Get_Inputs_Or_Proof_Ins return Node_Sets.Set;
      --  @return all Globals that are purely of mode Input or Proof_In

      function Get_Outputs return Node_Sets.Set;
      --  @return all Globals that are purely of mode Output

      function Get_In_Outs return Node_Sets.Set;
      --  @return all Globals that are of mode In_Out

      function Get_Proof_Ins return Node_Sets.Set;
      --  @return all Globals that are of mode Proof_In

      --  The functions that follow facilitate calculation of
      --  subprogram calls.

      function Get_Proof_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are only ever called in proof
      --  related vertices.

      function Get_Definite_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are definitely called

      procedure Get_Local_Variables_And_Subprograms
        (Local_Vars : out Node_Sets.Set;
         Local_Subs : out Node_Sets.Set);
      --  Traverses the tree under FA.Analyzed_Entity and gathers all
      --  object and subprogram declarations and puts them
      --  respectivelly under Local_Vars and Local_Subs.
      --  @param Local_Vars is populated with all local variables
      --  @param Local_Subs is populated with all local subprograms

      function Get_Local_Definite_Writes return Node_Sets.Set;
      --  Returns all local variables of the package that are definitely
      --  initialized once the package has been elaborated.

      function Subprograms_Without_Contracts
        (NS : Node_Sets.Set)
         return Node_Sets.Set;
      --  Returns a subset of NS that comprises those subprograms that
      --  have no user-provided Global or Depends contracts.
      --  @param NS is the initial set of subprograms that we opperate on
      --  @return a subset of NS that comprises those subprograms that
      --    have no user-provided Global or Depends contracts.

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
      begin
         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            --  We iterate over vertices in the PDG and remove from the set
            --  All_Proof_Ins those variables that are used on vertices not
            --  related to proof.

            declare
               use Attribute_Maps;
               A : constant Constant_Reference_Type := FA.Atr (V);

            begin
               if FA.PDG.Get_Key (V).Variant /= Final_Value
                 and then not A.Is_Proof
               then
                  All_Proof_Ins.Difference
                    (To_Node_Set (To_Entire_Variables (A.Variables_Used)));
               end if;
            end;
         end loop;

         return All_Proof_Ins;
      end Get_Proof_Ins;

      ---------------------------
      -- Get_Proof_Subprograms --
      ---------------------------

      function Get_Proof_Subprograms return Node_Sets.Set is
         All_Proof_Subprograms : Node_Sets.Set := FA.Direct_Calls;
      begin
         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            --  We go through all vertices in the graph and we
            --  subtract from the All_Proof_Subprograms set the
            --  subprograms that are called on vertices that are not
            --  related to proof.

            declare
               use Attribute_Maps;
               A : constant Constant_Reference_Type := FA.Atr (V);
            begin
               if not A.Is_Proof then
                  All_Proof_Subprograms :=
                    All_Proof_Subprograms - A.Subprograms_Called;
               end if;
            end;
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

      -----------------------------------------
      -- Get_Local_Variables_And_Subprograms --
      -----------------------------------------

      procedure Get_Local_Variables_And_Subprograms
        (Local_Vars : out Node_Sets.Set;
         Local_Subs : out Node_Sets.Set)
      is
         function Get_Object_Or_Subprogram_Declaration
           (N : Node_Id)
            return Traverse_Result;
         --  Picks up entities coming from object and subprogram
         --  declarations and adds them respectively to Local_Vars
         --  and Local_Subs.

         procedure Remove_PO_And_Task_Parts;
         --  Removes from Local_Vars these variables which are parts of a
         --  singleton protected object or a singleton task. We don't do this
         --  when we process tasks.

         ------------------------------------------
         -- Get_Object_Or_Subprogram_Declaration --
         ------------------------------------------

         function Get_Object_Or_Subprogram_Declaration
           (N : Node_Id)
            return Traverse_Result
         is
            function Hidden_In_Package (E : Entity_Id) return Boolean;
            --  Returns True if E is either declared in the private part of a
            --  package that has an Initializes aspect or in the private part
            --  of a package that has SPARK_Mode => Off.

            -----------------------
            -- Hidden_In_Package --
            -----------------------

            function Hidden_In_Package (E : Entity_Id) return Boolean is
            begin
               if Get_Flow_Scope (E).Section /= Private_Part then
                  --  Not in the private part
                  return False;
               end if;

               if FA.Kind in Kind_Package | Kind_Package_Body
                 and then Unique_Entity (Scope (E)) in
                            Unique_Entity (FA.Analyzed_Entity) |
                            Unique_Entity (FA.Spec_Entity)
               then
                  --  We always consider the private and body part of the
                  --  Analyzed_Entity itself.
                  return False;
               end if;

               --  Check if the enclosing scope has an Initializes aspect or
               --  has SPARK_Mode set to Off.
               declare
                  Scp : constant Entity_Id := Scope (E);
               begin
                  case Ekind (Scp) is
                     when E_Package =>
                        return
                          --  Enclosing scope has Initializes
                          Present (Get_Pragma (Scp, Pragma_Initializes))

                          --  Enclosing scope has SPARK_Mode => Off
                          or else not Private_Spec_In_SPARK (Scp);

                     when others    =>
                        return False;
                  end case;
               end;

            end Hidden_In_Package;

         --  Start of processing for Get_Object_Or_Subprogram_Declaration

         begin
            case Nkind (N) is
               when N_Object_Declaration =>
                  declare
                     E : constant Entity_Id := Defining_Entity (N);
                  begin
                     if Hidden_In_Package (E)
                       or else In_Generic_Actual (E)
                     then
                        --  We do not want to process:
                        --
                        --   * formals of nested instantiations,
                        --
                        --   * object declarations that occur in the private
                        --     part of nested packages that have an Initializes
                        --     aspect.
                        return Skip;
                     else
                        if Ekind (E) /= E_Constant then
                           Local_Vars.Include (E);
                        elsif Has_Variable_Input (Direct_Mapping_Id (E)) then
                           --  If the Full_View is present then add that
                           if Present (Full_View (E)) then
                              Local_Vars.Include (Full_View (E));
                           else
                              Local_Vars.Include (E);
                           end if;
                        end if;
                     end if;
                  end;

               when N_Loop_Parameter_Specification =>
                  --  Add variable introduced by for loop (but do not add
                  --  variables introduced by quantified expressions)
                  if Nkind (Parent (N)) /= N_Iteration_Scheme
                    or else Hidden_In_Package (Defining_Identifier (N))
                  then
                     return Skip;
                  else
                     Local_Vars.Include (Defining_Identifier (N));
                  end if;

               when N_Single_Task_Declaration |
                    N_Task_Type_Declaration   =>
                  if Unique_Entity (Defining_Identifier (N)) /=
                    Unique_Entity (FA.Analyzed_Entity)
                  then
                     Local_Subs.Include (Unique_Defining_Entity (N));
                     return Skip;
                  end if;

               when N_Entry_Declaration      |
                    N_Subprogram_Declaration =>
                  if Unique_Defining_Entity (N) /=
                    Unique_Entity (FA.Analyzed_Entity)
                  then
                     Local_Subs.Include (Unique_Defining_Entity (N));
                     return Skip;
                  end if;

               when N_Package_Declaration =>
                  --  State abstractions of nested packages appear as local
                  --  variables.
                  declare
                     AS_Pragma : constant Node_Id :=
                       Get_Pragma (Defining_Entity (N),
                                   Pragma_Abstract_State);

                     PAA       : Node_Id;
                     AS_N      : Node_Id;
                     AS_E      : Entity_Id;
                  begin
                     if Present (AS_Pragma) then
                        PAA  :=
                          First (Pragma_Argument_Associations (AS_Pragma));

                        --  Check that we don't have Abstract_State => null
                        if Nkind (Expression (PAA)) /= N_Null then
                           AS_N := First (Expressions (Expression (PAA)));

                           while Present (AS_N) loop
                              AS_E := (if Nkind (AS_N) = N_Extension_Aggregate
                                       then Entity (Ancestor_Part (AS_N))
                                       else Entity (AS_N));

                              Local_Vars.Include (AS_E);

                              Next (AS_N);
                           end loop;
                        end if;
                     end if;
                  end;

               when N_Package_Body      |
                    N_Package_Body_Stub =>
                  declare
                     Package_Spec : constant Entity_Id :=
                       (case Nkind (N) is
                        when N_Package_Body      => Corresponding_Spec (N),
                        when N_Package_Body_Stub =>
                          Corresponding_Spec_Of_Stub (N),
                        when others              => raise Program_Error);

                     AS_Pragma : constant Node_Id :=
                       Get_Pragma (Package_Spec, Pragma_Abstract_State);
                  begin
                     --  Skip bodies of generic packages
                     if Ekind (Package_Spec) = E_Generic_Package then
                        return Skip;
                     end if;

                     --  Skip bodies of packages that are not in SPARK
                     if not Entity_Body_In_SPARK (Package_Spec) then
                        return Skip;
                     end if;

                     --  Skip bodies of nested packages that have an abstract
                     --  state contract
                     if Present (AS_Pragma)
                       and then Unique_Defining_Entity (N) /=
                                  Unique_Entity (FA.Analyzed_Entity)
                     then
                        return Skip;
                     end if;
                  end;

               when N_Entry_Body |
                    N_Task_Body  =>
                  if Unique_Entity (Defining_Identifier (N)) /=
                    Unique_Entity (FA.Analyzed_Entity)
                  then
                     Local_Subs.Include
                       (Unique_Entity (Defining_Identifier (N)));
                     return Skip;
                  end if;

               when N_Subprogram_Body =>
                  if Unique_Defining_Entity (N) /=
                    Unique_Entity (FA.Analyzed_Entity)
                  then
                     Local_Subs.Include (Unique_Defining_Entity (N));
                     return Skip;
                  end if;

               when N_Handled_Sequence_Of_Statements =>
                  --  Skip statements of a nested package's body
                  if Nkind (Parent (N)) = N_Package_Body then
                     return Skip;
                  end if;

               when N_Generic_Package_Declaration    |
                    N_Generic_Subprogram_Declaration =>
                  --  Skip generic declarations
                  return Skip;

               when others =>
                  null;
            end case;

            return OK;
         end Get_Object_Or_Subprogram_Declaration;

         ------------------------------
         -- Remove_PO_And_Task_Parts --
         ------------------------------

         procedure Remove_PO_And_Task_Parts is
            Part_Of_Vars : Node_Sets.Set := Node_Sets.Empty_Set;
         begin
            if FA.Kind = Kind_Task then
               return;
            end if;

            for Var of Local_Vars loop
               if Is_Part_Of_Concurrent_Object (Var) then
                  Part_Of_Vars.Insert (Var);
               end if;
            end loop;

            Local_Vars := Local_Vars - Part_Of_Vars;
         end Remove_PO_And_Task_Parts;

         procedure Gather_Local_Variables_And_Subprograms is
            new Traverse_Proc (Get_Object_Or_Subprogram_Declaration);

      --  Start of processing for Get_Local_Variables_And_Subprograms

      begin
         --  Initialize Local_Vars and Local_Subs
         Local_Vars := Node_Sets.Empty_Set;
         Local_Subs := Node_Sets.Empty_Set;

         --  Gather formal parameters of the entry/subprogram/task or state
         --  abstractions of the package.
         case FA.Kind is
            when Kind_Subprogram | Kind_Entry | Kind_Task =>
               Local_Vars := Get_Formals (FA.Analyzed_Entity);

            when Kind_Package | Kind_Package_Body =>
               --  State abstractions of a package effectively act as local
               --  variables.
               declare
                  AS_Pragma : constant Node_Id :=
                    Get_Pragma (FA.Spec_Entity, Pragma_Abstract_State);

                  PAA       : Node_Id;
                  AS_N      : Node_Id;
                  AS_E      : Entity_Id;
               begin
                  if Present (AS_Pragma) then
                     PAA := First (Pragma_Argument_Associations (AS_Pragma));

                     --  Check that we don't have Abstract_State => null
                     if Nkind (Expression (PAA)) /= N_Null then
                        AS_N := First (Expressions (Expression (PAA)));
                        while Present (AS_N) loop
                           AS_E := (if Nkind (AS_N) = N_Extension_Aggregate
                                    then Entity (Ancestor_Part (AS_N))
                                    else Entity (AS_N));

                           Local_Vars.Insert (AS_E);

                           Next (AS_N);
                        end loop;
                     end if;
                  end if;
               end;
         end case;

         --  Gather local parameters and subprograms
         case FA.Kind is
            when Kind_Subprogram | Kind_Entry | Kind_Task =>
               Gather_Local_Variables_And_Subprograms
                 (Get_Body (FA.Analyzed_Entity));

            when Kind_Package | Kind_Package_Body =>
               declare
                  Decl : Entity_Id := FA.Spec_Entity;
               begin
                  while Nkind (Decl) not in N_Package_Declaration         |
                                            N_Generic_Package_Declaration
                    and then Present (Parent (Decl))
                  loop
                     Decl := Parent (Decl);
                  end loop;

                  pragma Assert (Nkind (Decl) in
                                   N_Package_Declaration         |
                                   N_Generic_Package_Declaration);

                  Gather_Local_Variables_And_Subprograms (Decl);

                  if FA.Kind = Kind_Package_Body then
                     Gather_Local_Variables_And_Subprograms
                       (Package_Body (FA.Analyzed_Entity));
                  end if;
               end;
         end case;

         --  Remove from Local_Vars the variables which are parts of singelton
         --  protected objects and singleton tasks.
         Remove_PO_And_Task_Parts;
      end Get_Local_Variables_And_Subprograms;

      -------------------------------
      -- Get_Local_Definite_Writes --
      -------------------------------

      function Get_Local_Definite_Writes return Node_Sets.Set is
         Definite_Local_Writes : Node_Sets.Set := Node_Sets.Empty_Set;
         FS                    : Flow_Id_Sets.Set;
         V_Initial             : Flow_Graphs.Vertex_Id;
         Guilty                : Boolean;
      begin
         for LV of Local_Variables loop
            --  We go through all local variables and check if their
            --  corresponding 'Initial vertex has no Out_Neighbours.

            Guilty := False;  --  Innocent till found guilty

            FS := Flatten_Variable (LV, FA.B_Scope);

            for Comp of FS loop
               V_Initial := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Initial_Value));

               pragma Assert (V_Initial /= Flow_Graphs.Null_Vertex);

               if FA.PDG.Out_Neighbour_Count (V_Initial) /= 0 then
                  Guilty := True;
                  exit;
               end if;
            end loop;

            if not Guilty then
               Definite_Local_Writes.Insert (LV);
            end if;
         end loop;

         return Definite_Local_Writes;
      end Get_Local_Definite_Writes;

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

   --  Start of processing for Compute_Globals

   begin
      Inputs_Proof          := Get_Proof_Ins;
      Inputs                := Get_In_Outs or (Get_Inputs_Or_Proof_Ins -
                                                 Get_Proof_Ins);
      Outputs               := Get_In_Outs or Get_Outputs;
      Proof_Calls           := Get_Proof_Subprograms;
      Definite_Calls        := Get_Definite_Subprograms - Proof_Calls;
      Conditional_Calls     := Subprograms_Without_Contracts
        (FA.Direct_Calls - Definite_Calls - Proof_Calls);

      Get_Local_Variables_And_Subprograms (Local_Variables, Local_Subprograms);

      Local_Definite_Writes := Get_Local_Definite_Writes;
   end Compute_Globals;

end Flow.Slice;
