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

with Common_Iterators;       use Common_Iterators;
with Flow_Utility;           use Flow_Utility;
with Sem_Aux;                use Sem_Aux;
with Sem_Type;               use Sem_Type;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Snames;                 use Snames;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
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
      --  If the visited vertex is an in vertex or a procedure parameter
      --  vertex, we add it to the set of things we depend on.

      -------------
      -- Visitor --
      -------------

      procedure Visitor
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         F : Flow_Id renames FA.PDG.Get_Key (V);
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

   --  Start of processing for Internal_Dependency

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
      Tmp : constant Vertex_Sets.Set :=
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
      --  Given a flow id, return the view the dependency relation cares about

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
      --  it out the Unused_Inputs set, so that we don't produce a
      --  flow error about a missing null dependency.

      DM            : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      use type Vertex_Sets.Set;

   --  Start of processing for Compute_Dependency_Relation

   begin

      --  Determine all out vertices

      for V_Final of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : Flow_Id renames FA.PDG.Get_Key (V_Final);
         begin
            if F_Final.Variant = Final_Value
              and then FA.Atr (V_Final).Is_Export
              and then not Synthetic (F_Final)
            then
               Out_Vertices.Include (V_Final);
            end if;
         end;
      end loop;

      --  Determine all input vertices

      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Initial : Flow_Id renames FA.PDG.Get_Key (V_Initial);
            Attr : V_Attributes renames FA.Atr (V_Initial);
         begin
            if F_Initial.Variant = Initial_Value
              and then Attr.Is_Import
              and then not Synthetic (F_Initial)
            then
               In_Vertices.Include (V_Initial);
               Unused_Inputs.Include (Flow_Equivalent (F_Initial));

               if (Is_Discriminant (F_Initial) or else Is_Bound (F_Initial))
                 and then Attr.Mode = Mode_Out
               then
                  --  See above about suppressing "null => foo" dependency
                  --  error messages for out parameters and globals.
                  Out_Discrim.Include
                    (Change_Variant (Entire_Variable (F_Initial),
                                     Normal_Use));
               end if;
            end if;
         end;
      end loop;

      --  Determine dependencies

      for V_Out of Out_Vertices loop
         declare
            F_In  : Flow_Id;
            F_Out : constant Flow_Id :=
              Flow_Equivalent (FA.PDG.Get_Key (V_Out));

            --  Compute dependencies (and filter out local variables)
            Deps : constant Vertex_Sets.Set :=
              Internal_Dependency (FA      => FA,
                                   V_Final => V_Out,
                                   IPFA    => False)
              and In_Vertices;

            F_Out_Position : Dependency_Maps.Cursor;
            Dummy          : Boolean;
            --  Dummy variables required by the container API

         begin
            --  Initialize map entry with empty set or do nothing if already
            --  an entry is already there.
            DM.Insert (Key      => F_Out,
                       Position => F_Out_Position,
                       Inserted => Dummy);

            for V_In of Deps loop
               F_In := Flow_Equivalent (FA.PDG.Get_Key (V_In));

               DM (F_Out_Position).Include (F_In);
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
      --  The "Get" functions that follow return sets of nodes that are purely
      --  of the mode described in their names. This is pointed out so as to
      --  prevent confusion between the functions and the formal parameters
      --  of Compute_Globals (where an Input could also appear as an Output).

      --  Utitlity functions for calculating subprogram calls

      function Get_Proof_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are only ever called in proof related
      --  vertices.

      function Get_Definite_Subprograms return Node_Sets.Set;
      --  Returns all subprograms that are definitely called

      procedure Get_Local_Variables_And_Subprograms
      with Global => (Output => (Local_Variables, Local_Subprograms));
      --  Traverses the tree under FA.Analyzed_Entity and gathers all object
      --  and subprogram declarations and puts them in Local_Variables and
      --  Local_Subprograms, respectively.

      procedure Get_Local_Definite_Writes;
      --  Collect local variables of the package that are definitely
      --  initialized after package elaboration.

      function Subprograms_Without_Contracts
        (NS : Node_Sets.Set)
         return Node_Sets.Set;
      --  Returns a subset of NS that comprises those subprograms that have no
      --  user-provided Global or Depends contracts.
      --  @param NS is the initial set of subprograms that we opperate on
      --  @return a subset of NS that comprises those subprograms that
      --    have no user-provided Global or Depends contracts.

      ---------------------------
      -- Get_Proof_Subprograms --
      ---------------------------

      function Get_Proof_Subprograms return Node_Sets.Set is
         All_Proof_Subprograms : Node_Sets.Set := FA.Direct_Calls;
      begin
         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            --  We exclude subprograms called in graph vertices not related to
            --  proof.

            declare
               A : V_Attributes renames FA.Atr (V);

            begin
               if not A.Is_Proof then
                  All_Proof_Subprograms.Difference (A.Subprograms_Called);
               end if;
            end;
         end loop;

         return Subprograms_Without_Contracts (All_Proof_Subprograms);
      end Get_Proof_Subprograms;

      ------------------------------
      -- Get_Definite_Subprograms --
      ------------------------------

      function Get_Definite_Subprograms return Node_Sets.Set is
         All_Definite_Subprograms : Node_Sets.Set := Node_Sets.Empty_Set;
      begin
         --  Collect those directly called subprograms whose corresponding
         --  'Initial vertex has no Out_Neighbours.

         for G of FA.Direct_Calls loop
            declare
               F         : constant Flow_Id := Direct_Mapping_Id (G);
               V_Initial : constant Flow_Graphs.Vertex_Id :=
                 FA.PDG.Get_Vertex (Change_Variant (F, Initial_Value));
            begin
               if FA.PDG.Out_Neighbour_Count (V_Initial) = 0 then
                  All_Definite_Subprograms.Insert (G);
               end if;
            end;
         end loop;

         return Subprograms_Without_Contracts (All_Definite_Subprograms);
      end Get_Definite_Subprograms;

      -----------------------------------------
      -- Get_Local_Variables_And_Subprograms --
      -----------------------------------------

      procedure Get_Local_Variables_And_Subprograms is
         function Get_Object_Or_Subprogram_Declaration
           (N : Node_Id)
            return Traverse_Result;
         --  Pick entities coming from object and subprogram declarations and
         --  add them respectively to Local_Variables and Local_Subprograms.
         --  ??? respect SPARK_Mode => Off

         procedure Delete_PO_And_Task_Parts;
         --  Delete those of Local_Variables that are Part_Of a singleton
         --  protected object or a singleton task. We don't do this when
         --  we process tasks.

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
               S : constant Flow_Scope := Get_Flow_Scope (E);
            begin
               return
                 Present (S)
                 and then S.Part = Private_Part
                 and then not (FA.Kind in Kind_Package | Kind_Package_Body
                               and then S.Ent = FA.Spec_Entity)
                 --  Always consider the private and body parts of the
                 --  Analyzed_Entity itself.

                 --  Check if the enclosing scope has an Initializes aspect
                 --  or has SPARK_Mode => Off.
                 and then Ekind (S.Ent) = E_Package
                 and then
                   (Present (Get_Pragma (S.Ent, Pragma_Initializes))
                    --  Enclosing scope has Initializes

                    or else not Private_Spec_In_SPARK (S.Ent)
                    --  Enclosing scope has SPARK_Mode => Off
                   );
            end Hidden_In_Package;

         --  Start of processing for Get_Object_Or_Subprogram_Declaration

         begin
            case Nkind (N) is
               when N_Entry_Body      |
                    N_Subprogram_Body |
                    N_Task_Body       =>
                  if Unique_Defining_Entity (N) /= FA.Spec_Entity then
                     return Skip;
                  end if;

               when N_Entry_Declaration      |
                    N_Subprogram_Declaration |
                    N_Task_Type_Declaration  =>
                  declare
                     E : constant Entity_Id := Defining_Entity (N);
                  begin
                     if E /= FA.Spec_Entity then
                        Local_Subprograms.Insert (E);
                        return Skip;
                     end if;
                  end;

               when N_Subprogram_Body_Stub =>
                  if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
                     Local_Subprograms.Insert (Defining_Entity (N));
                     return Skip;
                  end if;

               when N_Generic_Package_Declaration    |
                    N_Generic_Subprogram_Declaration =>
                  --  Skip generic declarations
                  return Skip;

               when N_Handled_Sequence_Of_Statements =>
                  --  Skip statements of a nested package's body
                  --  ???
                  if Nkind (Parent (N)) = N_Package_Body then
                     return Skip;
                  end if;

               when N_Loop_Parameter_Specification =>
                  --  Add variable introduced by FOR loop, but ignore variable
                  --  introduced by quantified expression (because that
                  --  expressions cannot define new callable entities for
                  --  which the variable would act as a global).
                  if Nkind (Parent (N)) = N_Iteration_Scheme then
                     declare
                        E : constant Entity_Id := Defining_Identifier (N);
                     begin
                        pragma Assert (not Hidden_In_Package (E));
                        Local_Variables.Insert (E);
                     end;
                  end if;

                  return Skip;

               when N_Object_Declaration =>
                  declare
                     E : constant Entity_Id := Defining_Entity (N);
                  begin
                     --  Ignore:
                     --
                     --   * formals of nested instantiations,
                     --
                     --   * object declarations that occur in the private
                     --     part of nested packages that have an Initializes
                     --     aspect.
                     if Hidden_In_Package (E)
                       or else In_Generic_Actual (E)
                     then
                        null;
                     else
                        case Ekind (E) is
                           when E_Variable =>
                              Local_Variables.Insert (E);

                           when E_Constant =>
                              --  ??? there is no point in checking both the
                              --  partial and the full views; also no need to
                              --  include the full view for the second time.
                              if Has_Variable_Input (E)
                              then
                                 --  If the Full_View is present then add that
                                 Local_Variables.Include
                                   (if Present (Full_View (E))
                                    then Full_View (E)
                                    else E);
                              end if;

                           when others =>
                              raise Program_Error;
                        end case;
                     end if;
                  end;

                  return Skip;

               when N_Package_Body      |
                    N_Package_Body_Stub =>
                  declare
                     E : constant Entity_Id := Unique_Defining_Entity (N);
                  begin
                     --  Skip bodies of generic packages
                     if Ekind (E) = E_Generic_Package

                       --  and bodies of packages that are not in SPARK
                       or else not Entity_Body_In_SPARK (E)

                       --  and bodies of nested packages with Abstract_State
                       --  contract.
                       or else
                       (E /= FA.Spec_Entity
                          and then
                             Present
                               (Get_Pragma (E, Pragma_Abstract_State)))
                     then
                        return Skip;
                     end if;
                  end;

               when N_Package_Declaration =>
                  --  State abstractions appear as local variables
                  for State of Iter (Abstract_States (Defining_Entity (N)))
                  loop
                     if not Is_Null_State (State) then
                        Local_Variables.Insert (State);
                     end if;
                  end loop;

               when N_Single_Protected_Declaration |
                    N_Single_Task_Declaration      =>
                  --  These nodes should never occur after expansion
                  raise Program_Error;

               when others =>
                  null;
            end case;

            return OK;
         end Get_Object_Or_Subprogram_Declaration;

         ------------------------------
         -- Delete_PO_And_Task_Parts --
         ------------------------------

         procedure Delete_PO_And_Task_Parts is
         begin
            if FA.Kind /= Kind_Task then
               declare
                  Part_Of_Vars : Node_Lists.List;
                  --  Containers with variables to be deleted; needed because
                  --  deleting an element while iterating over container would
                  --  tamper with cursors.

               begin
                  for Var of Local_Variables loop
                     if Is_Part_Of_Concurrent_Object (Var) then
                        Part_Of_Vars.Append (Var);
                     end if;
                  end loop;

                  for V of Part_Of_Vars loop
                     Local_Variables.Delete (V);
                  end loop;
               end;
            end if;
         end Delete_PO_And_Task_Parts;

         procedure Gather_Local_Variables_And_Subprograms is
            new Traverse_Proc (Get_Object_Or_Subprogram_Declaration);

      --  Start of processing for Get_Local_Variables_And_Subprograms

      begin
         --  Initialize Local_Variables and Local_Subprograms: collect formal
         --  parameters of the entry/subprogram/task.
         Local_Variables :=
           (if FA.Kind in Kind_Subprogram | Kind_Task
            then Get_Formals (FA.Analyzed_Entity)
            else Node_Sets.Empty_Set);

         Local_Subprograms := Node_Sets.Empty_Set;

         --  Gather local variables and subprograms
         case FA.Kind is
            when Kind_Subprogram | Kind_Task =>
               Gather_Local_Variables_And_Subprograms
                 (Get_Body (FA.Analyzed_Entity));

            when Kind_Package | Kind_Package_Body =>
               Gather_Local_Variables_And_Subprograms
                 (Package_Spec (FA.Spec_Entity));

               if FA.Kind = Kind_Package_Body then
                  Gather_Local_Variables_And_Subprograms
                    (Package_Body (FA.Analyzed_Entity));
               end if;
         end case;

         --  Delete from Local_Variables the variables which are parts of
         --  singelton protected objects and singleton tasks.
         Delete_PO_And_Task_Parts;
      end Get_Local_Variables_And_Subprograms;

      -------------------------------
      -- Get_Local_Definite_Writes --
      -------------------------------

      procedure Get_Local_Definite_Writes is
      begin
         --  Detect initialized local variables
         for LV of Local_Variables loop

            --  Null abstract states and abstract states with null refinements
            --  are trivially initialized but are not detected by the condition
            --  in the else branch. (??? why?)
            if Is_Null_State (LV)
              or else (Ekind (LV) = E_Abstract_State
                       and then Has_Null_Refinement (LV))
            then
               Local_Definite_Writes.Insert (LV);

            --  Check if the corresponding 'Initial vertex has no
            --  Out_Neighbours.

            else
               declare
                  Guilty    : Boolean := False;  --  Innocent till found guilty
                  V_Initial : Flow_Graphs.Vertex_Id;

               begin
                  for Comp of Flatten_Variable (LV, FA.B_Scope) loop
                     V_Initial := FA.PDG.Get_Vertex
                       (Change_Variant (Comp, Initial_Value));

                     if FA.PDG.Out_Neighbour_Count (V_Initial) /= 0 then
                        Guilty := True;
                        exit;
                     end if;
                  end loop;

                  if not Guilty then
                     Local_Definite_Writes.Insert (LV);
                  end if;
               end;
            end if;
         end loop;
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
               Subs_Without_Contracts.Insert (N);
            end if;
         end loop;

         return Subs_Without_Contracts;
      end Subprograms_Without_Contracts;

      Ordinary_Ins : Node_Sets.Set;

   --  Start of processing for Compute_Globals

   begin
      --  Detect ordinary inputs, i.e. non-proof ones
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         --  We iterate over vertices in the PDG and collect variables that are
         --  used on vertices unrelated to proof.

         declare
            A : V_Attributes renames FA.Atr (V);

         begin
            if FA.PDG.Get_Key (V).Variant = Final_Value or else A.Is_Proof
            then
               null;
            else
               Ordinary_Ins.Union
                 (To_Node_Set (To_Entire_Variables (A.Variables_Used)));
            end if;
         end;
      end loop;

      --  Classify globals into outs, ins and in_outs; also, insert "out" and
      --  "in_out" globals into Outputs, and "in" into Inputs.
      Inputs.Clear;
      Outputs.Clear;

      for G of FA.GG.Globals loop
         declare
            Is_Used    : Boolean := False;
            Is_Written : Boolean := False;
            --  Innocent till found guilty

            FS : constant Flow_Id_Sets.Set :=
              Flatten_Variable (Direct_Mapping_Id (G), FA.B_Scope);
            --  ??? why not Flatten_Variable (G, FA.B_Scope)?

            V_Initial, V_Final : Flow_Graphs.Vertex_Id;

         begin
            for Comp of FS loop
               V_Initial := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Initial_Value));

               --  If the corresponding 'Initial vertex has Out_Neighbours then
               --  it is used.

               Is_Used := Is_Used
                 or else FA.PDG.Out_Neighbour_Count (V_Initial) > 0;

               --  If the corresponding 'Final vertex has a single in neighbour
               --  who is the 'Initial vertex then it must be an input.

               V_Final := FA.PDG.Get_Vertex
                 (Change_Variant (Comp, Final_Value));

               Is_Written := Is_Written
                 or else
                   (not (FA.PDG.In_Neighbour_Count (V_Final) = 1
                         and then (for some V of FA.PDG.Get_Collection
                                   (V_Final,
                                    Flow_Graphs.In_Neighbours) =>
                                     V = V_Initial)));

               --  If everything is already known then exit early
               if Is_Used and Is_Written then
                  exit;
               end if;
            end loop;

            --  Insert global into appropriate containers

            if Is_Written then
               Outputs.Insert (G);

               if Is_Used then
                  Inputs.Insert (G);
               end if;
            else
               if Is_Used then
                  if Ordinary_Ins.Contains (G) then
                     Inputs.Insert (G);
                  else
                     Inputs_Proof.Insert (G);
                  end if;
               else
                  --  If not written and not used, then should not be a global
                  raise Program_Error;
               end if;
            end if;
         end;
      end loop;

      --  Classify subprogram calls into proof, definite and conditional ones
      Proof_Calls       := Get_Proof_Subprograms;
      Definite_Calls    := Get_Definite_Subprograms - Proof_Calls;
      Conditional_Calls := Subprograms_Without_Contracts
        (FA.Direct_Calls - Definite_Calls - Proof_Calls);

      Get_Local_Variables_And_Subprograms;

      --  Only needed for packages
      if FA.Kind in Kind_Package | Kind_Package_Body then
         Get_Local_Definite_Writes;
      end if;
   end Compute_Globals;

end Flow.Slice;
