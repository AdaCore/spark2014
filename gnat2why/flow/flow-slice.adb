------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Flow_Utility;           use Flow_Utility;
with Sem_Util;               use Sem_Util;
with Snames;                 use Snames;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;

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
   --  Helper function to compute the dependencies for a single vertex

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
            when Initial_Value =>
               Deps.Insert (V);

            --  Final values don't depend on each other and there is no
            --  self-dependency of V_Final, because the DFS skips the start
            --  vertex.

            when Final_Value =>
               raise Program_Error;
            when In_View | Out_View =>
               if IPFA then
                  Deps.Insert (V);
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
      FA.PDG.DFS (Start         => V_Final,
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
      with Pre  => F.Kind in Direct_Mapping
                           | Record_Field
                           | Magic_String,
           Post => Flow_Equivalent'Result.Kind in Direct_Mapping
                                                | Magic_String
                     and then
                   Flow_Equivalent'Result.Variant = Normal_Use;
      --  Given a flow id, return the view the dependency relation cares about

      ---------------------
      -- Flow_Equivalent --
      ---------------------

      function Flow_Equivalent (F : Flow_Id) return Flow_Id is
        (Change_Variant (Entire_Variable (F), Normal_Use));

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

      for V_Final of FA.CFG.Get_Collection
        (FA.End_Vertex, Flow_Graphs.Out_Neighbours)
      loop
         declare
            F_Final : Flow_Id renames FA.PDG.Get_Key (V_Final);

            function V_Initial return Flow_Graphs.Vertex_Id is
              (FA.PDG.Get_Vertex
                 (Change_Variant (F_Final, Initial_Value)))
            with Pure_Function;
            --  Returns the corresponding 'Initial vertex. We use this to
            --  detect uninitialized outputs; otherwise they would appear in
            --  the dependency relation as "X => null", which means that X is
            --  initialized with a literal constant.
            --
            --  Note: is a function and not a constant, because we can't always
            --  compute it; the Pure aspect avoids repeated calls.
            --
            --  ??? I think this should be done in Internal_Dependency, i.e. it
            --  should distinguish between an item not being written at all and
            --  being written with no data dependency.

         begin
            pragma Assert (F_Final.Variant = Final_Value);

            if FA.Atr (V_Final).Is_Export
              and then Is_Variable (F_Final)
              and then not Synthetic (F_Final)
              and then not
                (FA.PDG.In_Neighbour_Count (V_Final) = 1
                   and then
                 FA.PDG.Parent (V_Final) = V_Initial
                   and then
                 not FA.Atr (V_Initial).Is_Initialized)
            then
               Out_Vertices.Insert (V_Final);
            end if;
         end;
      end loop;

      --  Determine all input vertices

      for V_Initial of FA.CFG.Get_Collection
        (FA.Start_Vertex, Flow_Graphs.In_Neighbours)
      loop
         declare
            F_Initial : Flow_Id renames FA.PDG.Get_Key (V_Initial);
            Atr       : V_Attributes renames FA.Atr (V_Initial);

         begin
            pragma Assert (F_Initial.Variant = Initial_Value);

            if Atr.Is_Import
              and then Is_Variable (F_Initial)
              and then not Synthetic (F_Initial)
            then
               In_Vertices.Insert (V_Initial);
               Unused_Inputs.Include (Flow_Equivalent (F_Initial));

               --  ??? Maybe we don't need to special case discriminants and
               --  bounds and subtracts those separately from the other unused
               --  inputs. This could be refactored. Look at
               --  Internal_Dependency as well as that could deal with those
               --  cases.

               if (Is_Discriminant (F_Initial) or else Is_Bound (F_Initial))
                 and then Atr.Mode = Mode_Out
               then
                  --  See above about suppressing "null => foo" dependency
                  --  error messages for out parameters and globals.
                  Out_Discrim.Include (Flow_Equivalent (F_Initial));
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
            --  Initialize map entry with empty set or do nothing if an entry
            --  is already there.
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
      Globals               : out Global_Nodes;
      Proof_Calls           : out Node_Sets.Set;
      Definite_Calls        : out Node_Sets.Set;
      Conditional_Calls     : out Node_Sets.Set;
      Local_Definite_Writes : out Node_Sets.Set)
   is
      --  The "Get_" functions that follow collect nodes that are purely of the
      --  mode described in their names. This is pointed out so as to prevent
      --  confusion between the functions and the formal parameters of
      --  Compute_Globals (where an Input could also appear as an Output).

      --  Utitlity functions for calculating subprogram calls

      Unresolved : Node_Sets.Set;
      --  Direct calls whose flow effects (given in the Global or Depends
      --  contracts) are not already "inlined" in the control flow graph.

      procedure Get_Definite_Calls (Calls : out Node_Sets.Set)
      with Global => (Input => Unresolved);
      --  Get subprograms that are definitely called

      procedure Get_Local_Definite_Writes
      with Pre => FA.Kind = Kind_Package;
      --  Collect local variables of the package that are definitely
      --  initialized after package elaboration.

      ------------------------
      -- Get_Definite_Calls --
      ------------------------

      procedure Get_Definite_Calls (Calls : out Node_Sets.Set) is
      begin
         --  Collect those directly called subprograms whose corresponding
         --  'Initial vertex has no Out_Neighbours. Those vertices were created
         --  while post-processing the CFG, but only for callees that can write
         --  global objects (i.e. procedures and entries) and only those, whose
         --  Global/Depends contracts have not been "inlined" when building the
         --  CFG (and this was checked while collecting the Unresolved set).

         pragma Assert (Calls.Is_Empty);

         for G of Unresolved loop
            if Ekind (G) in E_Procedure | E_Entry then
               declare
                  V_Initial : Flow_Graphs.Vertex_Id renames
                    FA.PDG.Get_Vertex (Direct_Mapping_Id (G, Initial_Value));

               begin
                  if FA.PDG.Out_Neighbour_Count (V_Initial) = 0 then
                     Calls.Insert (G);
                  end if;
               end;
            end if;
         end loop;
      end Get_Definite_Calls;

      -------------------------------
      -- Get_Local_Definite_Writes --
      -------------------------------

      procedure Get_Local_Definite_Writes is

         function Is_Written (Comp : Flow_Id) return Boolean;
         --  Returns True iff Comp is definitely written, according to the PDG

         function Is_Empty (E : Entity_Id) return Boolean
         with Pre => Ekind (E) in E_Abstract_State | E_Constant | E_Variable;
         --  Returns True iff E has no components that could be "written"
         --  according to the flow graphs, but still should appear in the
         --  generated Initializes.

         function Is_Empty (E : Entity_Id) return Boolean is
           (case Ekind (E) is
               when E_Abstract_State =>
                  Has_Null_Refinement (E),
               --  ??? The intention is to check the Refined_State of the
               --  currently analysed package, but see what happens here:
               --
               --    package Outer with Abstract_State => Outer_State is
               --    private
               --       package Inner with Abstract_State => Inner_State is ...
               --       --  When analysing Outer we also peek into
               --       --  Inner_State's refinement, which is wrong.
               --    end Outer;

               when E_Constant | E_Variable =>
                  Is_Empty_Record_Type (Get_Type (E, FA.B_Scope)),

               when others =>
                  raise Program_Error);

         ----------------
         -- Is_Written --
         ----------------

         function Is_Written (Comp : Flow_Id) return Boolean is
            Comp_Initial : constant Flow_Graphs.Vertex_Id :=
              FA.PDG.Get_Vertex (Change_Variant (Comp, Initial_Value));

            Comp_Final   : constant Flow_Graphs.Vertex_Id :=
              FA.PDG.Get_Vertex (Change_Variant (Comp, Final_Value));
            --  'Initial and 'Final vertices for Comp, respectively

         begin
            --  It either can be initialized by default

            if FA.Atr (Comp_Initial).Is_Initialized then
               return True;

            --  otherwise, its final value can't depend on its initial value

            else
               return
                 not FA.PDG.Edge_Exists (Comp_Initial, Comp_Final);
            end if;
         end Is_Written;

      --  Start of processing for Get_Local_Definite_Writes

      begin
         --  Detect initialized local variables
         for LV of FA.GG.Local_Variables loop

            --  Abstract states with null refinements are trivially initialized
            --  but are not detected by the condition in the else branch. (???
            --  why?)

            if Is_Empty (LV) then
               Local_Definite_Writes.Insert (LV);

            else
               if (for all Comp of Flatten_Variable (LV, FA.B_Scope) =>
                     Is_Written (Comp))
               then
                  Local_Definite_Writes.Insert (LV);
               end if;
            end if;
         end loop;
      end Get_Local_Definite_Writes;

      Ordinary_Ins : Node_Sets.Set;

      Proof_Ins : Global_Set;
      Inputs    : Global_Set;
      Outputs   : Global_Set;
      --  Placeholders for the results; they are separate containers because
      --  while we populate them we don't want to care about the predicate on
      --  the result type.

   --  Start of processing for Compute_Globals

   begin
      --  Detect ordinary inputs, i.e. non-proof ones, and classify calls into
      --  proof and non-proof.
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         --  We iterate over vertices in the PDG and collect variables that are
         --  used on vertices unrelated to proof.

         declare
            A : V_Attributes renames FA.Atr (V);

         begin
            if FA.PDG.Get_Key (V).Variant = Final_Value or else A.Is_Assertion
            then
               null;
            else
               Ordinary_Ins.Union
                 (To_Node_Set (To_Entire_Variables (A.Variables_Used)));
            end if;

            for E of A.Subprograms_Called loop

               pragma Assert (Ekind (E) in Entry_Kind
                                         | E_Function
                                         | E_Procedure
                                         | E_Package);

               --  We don't expect calls to predicate functions in the CFG

               pragma Assert (if Ekind (E) = E_Function
                              then not Is_Predicate_Function (E));

               --  Nested packages with Initializes contract have their reads
               --  and writes are already inlined in the CFG; those without the
               --  that contract need to be processed by the GG just like
               --  subprogram calls.

               if Ekind (E) = E_Package then
                  if No (Get_Pragma (E, Pragma_Initializes)) then
                     Unresolved.Insert (E);
                  end if;

               --  For ordinary subprograms, check if their flow effects
               --  have been already "inlined" in CFG; see the call
               --  to Process_Subprogram_Globals in Do_Call_Statement.
               --  ??? refactor those to using a common routine

               else
                  if not Has_User_Supplied_Globals (E)
                    or else Rely_On_Generated_Global (E, FA.B_Scope)
                  then
                     if A.Is_Assertion then
                        Proof_Calls.Include (E);
                     else
                        Unresolved.Include (E);
                     end if;
                  end if;
               end if;
            end loop;
         end;
      end loop;

      --  Calls called both in proof and non-proof contexts are non-proof calls
      Proof_Calls.Difference (Unresolved);

      Get_Definite_Calls (Definite_Calls);

      Conditional_Calls := Unresolved;
      Conditional_Calls.Difference (Definite_Calls);

      --  Classify globals into outs, ins and in_outs; also, insert "out" and
      --  "in_out" globals into Outputs, and "in" into Inputs.

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
                         and then FA.PDG.Parent (V_Final) = V_Initial));

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
                     Proof_Ins.Insert (G);
                  end if;
               else
                  --  If not written and not used, then should not be a global
                  raise Program_Error;
               end if;
            end if;
         end;
      end loop;

      Globals := (Proof_Ins => Proof_Ins,
                  Inputs    => Inputs,
                  Outputs   => Outputs);

      --  Only needed for packages
      if FA.Kind = Kind_Package then
         Get_Local_Definite_Writes;
      end if;
   end Compute_Globals;

end Flow.Slice;
