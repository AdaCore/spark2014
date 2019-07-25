------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
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

with Elists;                      use Elists;
with Lib;                         use Lib;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Output;                      use Output;
with Restrict;                    use Restrict;
with Rident;                      use Rident;
with Sem_Aux;                     use Sem_Aux;
with Sem_Type;                    use Sem_Type;
with Sem_Util;                    use Sem_Util;
with Sem_Warn;                    use Sem_Warn;
with Snames;                      use Snames;

with Common_Iterators;            use Common_Iterators;
with SPARK_Annotate;              use SPARK_Annotate;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Frame_Conditions;      use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Types;            use SPARK_Util.Types;
with VC_Kinds;                    use VC_Kinds;

with Flow.Analysis.Antialiasing;
with Flow.Analysis.Sanity;
with Flow.Slice;                     use Flow.Slice;
with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Utility;                   use Flow_Utility;
with Flow_Utility.Initialization;    use Flow_Utility.Initialization;

package body Flow.Analysis is

   Debug_Trace_Depends     : constant Boolean := False;
   --  Enable this to show the specified and computed dependency relation

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Dependency_Path (FA      : Flow_Analysis_Graphs;
                             Input   : Flow_Id;
                             Outputs : Flow_Id_Sets.Set)
                             return Vertex_Sets.Set
   with Pre => not Outputs.Is_Empty,
        Post => not Vertex_Sets.Contains (Dependency_Path'Result,
                                          Flow_Graphs.Get_Vertex (FA.PDG,
                                                                  Input))
                and then
                  (for all O of Outputs
                   => not Vertex_Sets.Contains
                            (Dependency_Path'Result,
                             Flow_Graphs.Get_Vertex (FA.PDG, O)));
   --  Finds the shortest path in the PDG graph connecting vertex Input and
   --  Outputs or a vertex that defines one of the variables in Output. Returns
   --  the vertices in this path (Input and Outputs excluded).

   function Find_Global
     (S : Entity_Id;
      F : Flow_Id) return Node_Or_Entity_Id
   with Pre => Ekind (S) in Entry_Kind
                          | E_Function
                          | E_Package
                          | E_Procedure
                          | E_Task_Type;
   --  Find the global F in the Global, Refined_Global, or Initializes aspect
   --  of S. If it is not there (perhaps because it comes from computed
   --  globals) just return S which is a good fallback location for error
   --  reports.
   --
   --  ??? In some context where this routine is used we should also scan the
   --  Refined_Depends and Depends contracts, in particular when they are used
   --  as a substitute for a missing Refined_Global/Global, e.g. Analyse_Main.
   --
   --  ??? in some calls to this routine the F is a constituent while the
   --  contract references its abstract state; should be fixed either in
   --  Find_Global or in its callers.

   function Get_Initial_Vertex (G : Flow_Graphs.Graph;
                                F : Flow_Id)
                                return Flow_Graphs.Vertex_Id
   with Pre  => F.Variant = Normal_Use,
        Post => Get_Initial_Vertex'Result = Flow_Graphs.Null_Vertex
                  or else G.Get_Key (Get_Initial_Vertex'Result).Variant in
                            Initial_Value | Initial_Grouping;
   --  Returns the vertex id which represents the initial value for F

   function Is_Param_Of_Null_Subp_Of_Generic (E : Entity_Id)
                                              return Boolean
   with Pre => Nkind (E) in N_Entity;
   --  Returns True iff E is a parameter of a formal subprogram of a generic
   --  unit and the formal subprogram has null default.

   function Has_Effects (FA : Flow_Analysis_Graphs) return Boolean
   with Pre => FA.Kind in Kind_Subprogram | Kind_Task;
   --  Returns True iff FA represents a task or a subprogram with effects.
   --  Certain analysis are only enabled if this is the case; otherwise we
   --  would spam the user with error messages for almost every statement.

   procedure Warn_On_Subprogram_With_No_Effect
     (FA : in out Flow_Analysis_Graphs)
   with Pre => FA.Kind = Kind_Subprogram
               and then not Has_Effects (FA);
   --  Issue a warning if the subprogram has no effects. The message is
   --  suppressed if the subprogram is:
   --  * a ghost entity
   --  * is marked No_Return and is considered to always terminate abnormally
   --  * is annotated with globals by the user.

   -----------------
   -- Has_Effects --
   -----------------

   function Has_Effects (FA : Flow_Analysis_Graphs) return Boolean is
     (FA.Kind = Kind_Task
      or else
        (for some V of FA.CFG.Get_Collection (FA.End_Vertex,
                                              Flow_Graphs.Out_Neighbours)
         => FA.Atr (V).Is_Export));

   ---------------------
   -- Dependency_Path --
   ---------------------

   function Dependency_Path (FA      : Flow_Analysis_Graphs;
                             Input   : Flow_Id;
                             Outputs : Flow_Id_Sets.Set)
                             return Vertex_Sets.Set
   is
      Vertices : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Add_Loc (V : Flow_Graphs.Vertex_Id);
      --  Step procedure for Shortest_Path

      procedure Are_We_There_Yet
        (V           : Flow_Graphs.Vertex_Id;
         Instruction : out Flow_Graphs.Traversal_Instruction);
      --  Visitor procedure for Shortest_Path

      -------------
      -- Add_Loc --
      -------------

      procedure Add_Loc (V : Flow_Graphs.Vertex_Id) is
         F   : Flow_Id renames FA.PDG.Get_Key (V);
         Atr : V_Attributes renames FA.Atr (V);
      begin
         if F /= Input
           and then not Outputs.Contains (F)
           and then Atr.Is_Program_Node
         then
            Vertices.Insert (V);
         end if;
      end Add_Loc;

      ----------------------
      -- Are_We_There_Yet --
      ----------------------

      procedure Are_We_There_Yet
        (V           : Flow_Graphs.Vertex_Id;
         Instruction : out Flow_Graphs.Traversal_Instruction)
      is
         F   : Flow_Id renames FA.PDG.Get_Key (V);
         Atr : V_Attributes renames FA.Atr (V);
      begin
         if Outputs.Contains (F)
           or else (for some Var of Atr.Variables_Defined
                    => Outputs.Contains (Var))
         then
            Instruction := Flow_Graphs.Found_Destination;
         else
            Instruction := Flow_Graphs.Continue;
         end if;
      end Are_We_There_Yet;

   --  Start of processing for Dependency_Path

   begin
      FA.PDG.Shortest_Path (Start         => Get_Initial_Vertex (FA.PDG,
                                                                 Input),
                            Allow_Trivial => False,
                            Search        => Are_We_There_Yet'Access,
                            Step          => Add_Loc'Access);

      return Vertices;
   end Dependency_Path;

   -----------------
   -- Find_Global --
   -----------------

   function Find_Global
     (S : Entity_Id;
      F : Flow_Id) return Node_Or_Entity_Id
   is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            declare
               Target : constant Entity_Id := Get_Direct_Mapping_Id (F);
               Result : Node_Or_Entity_Id := S;
               --  Either the fallback entity S or a node that represents F
               --  in the contract.

               function Process (N : Node_Id) return Traverse_Result;
               --  Checks if N refers to Target and sets Result to N if that is
               --  the case.

               -------------
               -- Process --
               -------------

               function Process (N : Node_Id) return Traverse_Result is
               begin
                  --  The extra check for empty Entity filters the 'Global' and
                  --  'Refined_Global', i.e. the identifiers of the contract
                  --  aspect themselves.

                  if Nkind (N) in N_Identifier | N_Expanded_Name
                    and then Present (Entity (N))
                    and then Canonical_Entity (Ref     => Entity (N),
                                               Context => S) = Target
                  then
                     Result := N;
                     return Abandon;
                  else
                     return OK;
                  end if;
               end Process;

               procedure Traverse is new Traverse_More_Proc (Process);

            begin
               --  For packages scan the Initializes contract

               if Ekind (S) = E_Package then
                  Traverse (Get_Pragma (S, Pragma_Initializes));

               --  For other entities scan Refined_Global and Global

               else
                  Traverse (Find_Contract (S, Pragma_Refined_Global));

                  if Result /= S then
                     return Result;
                  end if;

                  Traverse (Find_Contract (S, Pragma_Global));
               end if;

               return Result;
            end;

         when Magic_String =>
            return S;

         when Null_Value | Synthetic_Null_Export =>
            raise Program_Error;

      end case;
   end Find_Global;

   ------------------------
   -- Get_Initial_Vertex --
   ------------------------

   function Get_Initial_Vertex
     (G : Flow_Graphs.Graph;
      F : Flow_Id)
      return Flow_Graphs.Vertex_Id
   is
      Initial_Value_Vertex : constant Flow_Graphs.Vertex_Id :=
        G.Get_Vertex (Change_Variant (F, Initial_Value));

   begin
      --  Look for either the Initial_Value or Initial_Grouping variant
      if Initial_Value_Vertex = Flow_Graphs.Null_Vertex then
         return G.Get_Vertex (Change_Variant (F, Initial_Grouping));
      else
         return Initial_Value_Vertex;
      end if;
   end Get_Initial_Vertex;

   ---------------------------------------
   -- Warn_On_Subprogram_With_No_Effect --
   ---------------------------------------

   procedure Warn_On_Subprogram_With_No_Effect
     (FA : in out Flow_Analysis_Graphs)
   is
   begin
      if not FA.Is_Main
        and then not Is_Error_Signaling_Procedure (FA.Analyzed_Entity)
        and then not Has_User_Supplied_Globals (FA.Analyzed_Entity)
        and then not Is_Ghost_Entity (FA.Analyzed_Entity)
      then
         Error_Msg_Flow
           (FA       => FA,
            Msg      => "subprogram & " & "has no effect",
            N        => FA.Analyzed_Entity,
            F1       => Direct_Mapping_Id (FA.Analyzed_Entity),
            Tag      => Ineffective,
            Severity => Warning_Kind);
      end if;
   end Warn_On_Subprogram_With_No_Effect;

   ------------------------
   -- First_Variable_Use --
   ------------------------

   function First_Variable_Use
     (N        : Node_Id;
      Scope    : Flow_Scope;
      Var      : Flow_Id;
      Precise  : Boolean;
      Targeted : Boolean := False) return Node_Id
   is
      Search_Under : Node_Id := N;
      First_Use    : Node_Id := N;
      Var_Tgt      : constant Flow_Id :=
        Change_Variant ((if Precise then Var else Entire_Variable (Var)),
                        Normal_Use);

      function Search_Expr (N : Node_Id) return Traverse_Result;
      --  Sets First_Use to the given node if it contains the variable we're
      --  looking for. If not, we abort the search.

      -----------------
      -- Search_Expr --
      -----------------

      function Search_Expr (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) in N_Subprogram_Call
                       | N_Entry_Call_Statement
                       | N_Expanded_Name
                       | N_Identifier
                       | N_Selected_Component
         then
            if Get_Variables (N,
                              Scope                => Scope,
                              Reduced              => not Precise,
                              Assume_In_Expression => False,
                              Fold_Functions       => False,
                              Use_Computed_Globals => True).Contains (Var_Tgt)
            then
               First_Use := N;
               return OK;
            else
               return Skip;
            end if;

         --  Calling Get_Variables can be very slow. Let's only do it on nodes
         --  that actually make sense to flag up in an check/info message from
         --  flow; i.e. nodes that describe a variable/constant or might use a
         --  global.

         else
            return OK;
         end if;
      end Search_Expr;

      procedure Search_Expression is new Traverse_More_Proc (Search_Expr);
      --  This will narrow down the location of the searched for
      --  variable in the given node as far as possible.

   --  Start of processing for First_Variable_Use

   begin
      if Targeted then
         case Nkind (N) is
            when N_Assignment_Statement =>
               Search_Under := Expression (N);

            when N_If_Statement =>
               Search_Under := Condition (N);

            when others =>
               null;
         end case;
      end if;

      Search_Expression (Search_Under);
      return First_Use;
   end First_Variable_Use;

   function First_Variable_Use
     (FA      : Flow_Analysis_Graphs;
      Var     : Flow_Id;
      Kind    : Var_Use_Kind;
      Precise : Boolean) return Node_Id
   is
      Var_Normal   : constant Flow_Id := Change_Variant (Var, Normal_Use);
      E_Var_Normal : constant Flow_Id := Entire_Variable (Var_Normal);

      First_Use : Node_Id := FA.Analyzed_Entity;

      procedure Proc
        (V      : Flow_Graphs.Vertex_Id;
         Origin : Flow_Graphs.Vertex_Id;
         Depth  : Natural;
         T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Checks if vertex V contains a reference to Var. If so, we
      --  set First_Use and abort the search.

      ----------
      -- Proc --
      ----------

      procedure Proc
        (V      : Flow_Graphs.Vertex_Id;
         Origin : Flow_Graphs.Vertex_Id;
         Depth  : Natural;
         T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         pragma Unreferenced (Origin, Depth);

         Atr : V_Attributes renames FA.Atr (V);

         function Of_Interest return Boolean;
         --  Returns True iff the current vertex contains the variable of
         --  interest.

         -----------------
         -- Of_Interest --
         -----------------

         function Of_Interest return Boolean is
            Check_Read  : constant Boolean := Kind in Use_Read  | Use_Any;
            Check_Write : constant Boolean := Kind in Use_Write | Use_Any;

            function Var_Is_In (Vars : Flow_Id_Sets.Set) return Boolean is
               (Vars.Contains (Var_Normal) or else
                  (not Precise and then
                     To_Entire_Variables (Vars).Contains (E_Var_Normal)));

         --  Start of processing for Of_Interest

         begin
            return
              (Check_Read  and then Var_Is_In (Atr.Variables_Used))
                 or else
              (Check_Write and then Var_Is_In (Atr.Variables_Defined));
         end Of_Interest;

      --  Start of processing for Proc

      begin
         if not Of_Interest then
            T_Ins := Flow_Graphs.Continue;
            return;
         else
            T_Ins := Flow_Graphs.Abort_Traversal;
         end if;

         --  Not all vertices containing the variable are actually interesting.
         --  We want to deal only with program statements and procedure calls.

         if (Atr.Is_Program_Node
               or Atr.Is_Assertion) and
           not Atr.Is_Callsite
         then
            if Present (FA.CFG.Get_Key (V)) then
               First_Use := Get_Direct_Mapping_Id (FA.CFG.Get_Key (V));
            else
               First_Use := FA.Atr (V).Error_Location;
            end if;
         elsif Atr.Is_Parameter then
            First_Use := Get_Direct_Mapping_Id (Atr.Parameter_Actual);
         elsif Atr.Is_Global_Parameter then
            --  If we have a global, the procedure call itself is the best
            --  location we can provide.
            First_Use := Get_Direct_Mapping_Id (Atr.Call_Vertex);
            return;
         else
            --  If we don't have any of the above, we should keep searching for
            --  other, more suitable, vertices.
            T_Ins := Flow_Graphs.Continue;
            return;
         end if;

         --  We have found a suitable vertex. We can now narrow down the
         --  location to the individual subexpression which contains the
         --  variable.

         case Nkind (First_Use) is
            when N_If_Statement | N_Elsif_Part =>
               First_Use := Condition (First_Use);

            when N_Case_Statement =>
               First_Use := Expression (First_Use);

            when N_Loop_Statement =>
               First_Use := Iteration_Scheme (First_Use);

            when others =>
               null;
         end case;

         First_Use := First_Variable_Use (N       => First_Use,
                                          Scope   => FA.B_Scope,
                                          Var     => Var,
                                          Precise => Precise);
      end Proc;

   --  Start of processing for First_Variable_Use

   begin
      FA.CFG.BFS (Start         => FA.Start_Vertex,
                  Include_Start => False,
                  Visitor       => Proc'Access);
      return First_Use;
   end First_Variable_Use;

   -------------------
   -- Has_Pragma_Un --
   -------------------

   function Has_Pragma_Un (E : Entity_Id) return Boolean is
   (Has_Pragma_Unmodified (E)
      or else Has_Pragma_Unreferenced (E)
      or else Has_Pragma_Unused (E));
   --  Checks if the entity E has been mentioned in any pragma Unmodified,
   --  Unreferenced or Unused.

   --------------------------------------
   -- Is_Param_Of_Null_Subp_Of_Generic --
   --------------------------------------

   function Is_Param_Of_Null_Subp_Of_Generic (E : Entity_Id) return Boolean is
   begin
      if Is_Formal (E) then
         declare
            Subp : constant Entity_Id := Scope (E);
         begin
            return Ekind (Subp) in E_Procedure | E_Function
              and then Is_Generic_Actual_Subprogram (Subp)
              and then Null_Present (Subprogram_Specification (Subp));
         end;
      else
         return False;
      end if;
   end Is_Param_Of_Null_Subp_Of_Generic;

   ------------------
   -- Analyse_Main --
   ------------------

   procedure Analyse_Main (FA : in out Flow_Analysis_Graphs) is
      Msg : constant String :=
        "& might not be initialized " &
        (case FA.Kind is
            when Kind_Subprogram =>
               "after elaboration of main program &",
            when Kind_Task =>
               "before start of tasks of type &",
            when others =>
               raise Program_Error);

      procedure Check_If_Initialized (R : Flow_Id);
      --  Emit error message if R is not initialized at elaboration

      --------------------------
      -- Check_If_Initialized --
      --------------------------

      procedure Check_If_Initialized (R : Flow_Id) is
      begin
         if not Is_Initialized_At_Elaboration (R, FA.B_Scope) then
            Error_Msg_Flow
              (FA       => FA,
               Msg      => Msg,
               N        => First_Variable_Use (FA      => FA,
                                               Var     => R,
                                               Kind    => Use_Read,
                                               Precise => True),
               F1       => R,
               F2       => Direct_Mapping_Id (FA.Spec_Entity),
               Tag      => Uninitialized,
               Severity => Medium_Check_Kind);
         end if;
      end Check_If_Initialized;

      --  Local variables

      Globals : Global_Flow_Ids;

   --  Start of processing for Analyse_Main

   begin
      --  Check if all global reads are initialized, i.e. that the following
      --  holds:
      --     Proof_In -> initialized
      --     Input    -> initialized
      --     Output   -> always OK
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Globals    => Globals);

      --  Proof_Reads and Reads are disjoint, iterate over their contents
      --  separately.

      for R of Globals.Proof_Ins loop
         Check_If_Initialized (R);
      end loop;

      for R of Globals.Inputs loop
         Check_If_Initialized (R);
      end loop;
   end Analyse_Main;

   ------------------
   -- Sanity_Check --
   ------------------

   procedure Sanity_Check
     (FA   : in out Flow_Analysis_Graphs;
      Sane :    out Boolean)
   is
      type Sanity_Check is access procedure
        (FA   : in out Flow_Analysis_Graphs;
         Sane :    out Boolean);

      type Sanity_Checks_T is array (Positive range <>) of Sanity_Check;

      Sanity_Checks : constant Sanity_Checks_T :=
        (Sanity.Check_Function_Side_Effects'Access,
         Sanity.Check_Expressions'Access,
         Sanity.Check_Generated_Refined_Global'Access,
         Sanity.Check_Illegal_Writes'Access,
         Sanity.Check_All_Variables_Known'Access,
         Sanity.Check_Side_Effects_In_Protected_Functions'Access);
   begin
      for C of Sanity_Checks loop
         C (FA, Sane);
         exit when not Sane;
      end loop;
   end Sanity_Check;

   --------------------------------
   -- Sanity_Check_Postcondition --
   --------------------------------

   procedure Sanity_Check_Postcondition (FA   : in out Flow_Analysis_Graphs;
                                         Sane : in out Boolean)
   is
   begin
      for Refined in Boolean loop
         declare
            Aspect_To_Fix : constant String :=
              (case FA.Kind is
               when Kind_Subprogram =>
                  (if Refined
                   then "Refined_Global"
                   else "Global"),

               when Kind_Package
                  | Kind_Package_Body
               =>
                  "Initializes",

               when Kind_Task =>
                  raise Program_Error);

            SRM_Ref : constant String :=
              (case FA.Kind is
               when Kind_Subprogram   => "6.1.4(14)",
               when Kind_Package
                  | Kind_Package_Body => "7.1.5(11)",
               when Kind_Task         => raise Program_Error);

            Vars_Used  : Flow_Id_Sets.Set;
            Vars_Known : Flow_Id_Sets.Set;

         begin
            if Refined then
               Vars_Known := To_Entire_Variables (FA.All_Vars);
               --  Copy all variables introduced into the flow graph, i.e.
               --  globals, formals and implicit 'Result (for functions).
               --  Note: we also copy local objects, which is unnecessary but
               --  harmless, because they can't be referenced in Post anyway.

            else
               case FA.Kind is
                  when Kind_Subprogram =>
                     --  We need to assemble the variables known from the spec:
                     --  parameters (both explicit and implicit), globals and
                     --  the implicit 'Result (for functions).

                     Vars_Known :=
                       To_Flow_Id_Set (Get_Formals (FA.Analyzed_Entity));

                     if Ekind (FA.Spec_Entity) = E_Function then
                        Vars_Known.Insert (Direct_Mapping_Id (FA.Spec_Entity));
                     end if;

                     declare
                        Globals : Global_Flow_Ids;

                     begin
                        Get_Globals (Subprogram => FA.Spec_Entity,
                                     Scope      => FA.S_Scope,
                                     Classwide  => False,
                                     Globals    => Globals);

                        --  Globals are disjoint except for an overlap between
                        --  inputs and outputs (which cannot be union-ed
                        --  because they differ in Flow_Id_Variant), so
                        --  iterate over sets one-by-one.

                        for F of Globals.Proof_Ins loop
                           Vars_Known.Insert (Change_Variant (F, Normal_Use));
                        end loop;

                        for F of Globals.Inputs loop
                           Vars_Known.Insert (Change_Variant (F, Normal_Use));
                        end loop;

                        for F of Globals.Outputs loop
                           Vars_Known.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;

                  when Kind_Package | Kind_Package_Body =>
                     Vars_Known :=
                       Down_Project (To_Entire_Variables (FA.Visible_Vars),
                                     FA.S_Scope);

                  when Kind_Task =>
                     raise Program_Error;
               end case;
            end if;

            for Expr of Get_Postcondition_Expressions (FA.Spec_Entity,
                                                       Refined)
            loop
               Vars_Used :=
                 To_Entire_Variables
                   (Get_Variables
                      (Expr,
                       Scope                => (if Refined
                                                then FA.B_Scope
                                                else FA.S_Scope),
                       Fold_Functions       => False,
                       Use_Computed_Globals => True));

               for Var of Vars_Used loop
                  if not Vars_Known.Contains (Var) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& must be listed in the " &
                                      Aspect_To_Fix & " aspect of &",
                        SRM_Ref  => SRM_Ref,
                        N        => First_Variable_Use (N       => Expr,
                                                        Scope   => FA.B_Scope,
                                                        Var     => Var,
                                                        Precise => False),
                        F1       => Var,
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Global_Wrong,
                        Severity => High_Check_Kind);
                     Sane := False;

                  elsif FA.Kind in Kind_Package | Kind_Package_Body
                    and then Is_Library_Level_Entity (FA.Analyzed_Entity)
                    and then not Is_Initialized_At_Elaboration (Var,
                                                                FA.B_Scope)
                  then

                     --  To check an Initial_Condition aspect, we make sure
                     --  that all variables mentioned are also mentioned in
                     --  an initializes aspect.

                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& must be initialized at elaboration",
                        N        => First_Variable_Use (N       => Expr,
                                                        Scope   => FA.B_Scope,
                                                        Var     => Var,
                                                        Precise => False),
                        F1       => Entire_Variable (Var),
                        Severity => Error_Kind);
                     Sane := False;

                  end if;

               end loop;
            end loop;
         end;
      end loop;

   end Sanity_Check_Postcondition;

   ----------------------------
   -- Find_Unwritten_Exports --
   ----------------------------

   procedure Find_Unwritten_Exports (FA : in out Flow_Analysis_Graphs) is

      --  This procedure deals with unwritten local and global entities.
      --
      --  For local entities (e.g. OUT parameters) we analyse the status at the
      --  level of record components, but emit messages at the level of entire
      --  variables.
      --
      --  For global entities in generative mode we shall get no errors
      --  (because the generated Global contract should be correct), but the
      --  algorithm is sometimes tricked by broken visibility with Entity_Names
      --  and by calls to procedures with No_Return and no Global contract. (We
      --  pull globals from such procedures in phase 1, but prune the calls in
      --  phase 2 if their Outputs happens to be empty). We conservatively emit
      --  messages to hint the user that something went wrong; we do this at
      --  the level of entire variables, for consistency with local entities.
      --
      --  For global entities with user-written contract (either Global/Depends
      --  or their refined variants), we emit messages at the level of entities
      --  that appear in the contracts; in particular, partially-visible
      --  constituent might appear in the contract directly, or optionally via
      --  its encapsulating state (or via the encapsulating state of its state,
      --  etc.) We can't deal with those options using the up/down-projection.
      --  Instead, we rely on what is directly written in the contract, and for
      --  this direct access we bypass the Get_Globals, because it involves
      --  down-projection.

      Unwritten_Vars : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      Unwritten_Global_Exports : Node_Sets.Set;
      Written_Exports          : Flow_Id_Sets.Set;
      --  ??? would be better to have those symmetric, but even better, we
      --  should reuse more code with Find_Ineffective_Imports_...

      function Is_In_Access_Parameter (E : Entity_Id) return Boolean;
      --  Returns True iff E is a formal parameter of mode IN with a named
      --  access type. Such parameters appear as exports (except if they are
      --  access-to-constant) and they can be written, but they are typically
      --  used without being written and then we suppress the warning.

      function Is_Or_Belongs_To_Concurrent_Object
        (F : Flow_Id)
         return Boolean
      with Pre => F.Kind in Direct_Mapping | Record_Field;
      --  @param F is the Flow_Id that we want to check
      --  @return True iff F is or belongs to a concurrent object

      ----------------------------
      -- Is_In_Access_Parameter --
      ----------------------------

      function Is_In_Access_Parameter (E : Entity_Id) return Boolean is
      begin
         if Ekind (E) = E_In_Parameter then
            declare
               Typ : constant Entity_Id := Get_Type (E, FA.B_Scope);

            begin
               --  Access constant types never appear as exports
               pragma Assert (not Is_Access_Constant (Typ));

               return Is_Access_Type (Typ)
                 and then not Is_Anonymous_Access_Type (Typ);
            end;
         else
            return False;
         end if;
      end Is_In_Access_Parameter;

      ----------------------------------------
      -- Is_Or_Belongs_To_Concurrent_Object --
      ----------------------------------------

      function Is_Or_Belongs_To_Concurrent_Object
        (F : Flow_Id)
         return Boolean
      is
        (Is_Concurrent_Type (Get_Direct_Mapping_Id (F)));

   --  Start of processing for Find_Unwritten_Exports

   begin
      --  When checking against a user-written Global/Depends we get the
      --  globals directly from that contract.

      if not FA.Is_Generative then
         Unwritten_Global_Exports := Contract_Globals (FA.Spec_Entity).Outputs;
      end if;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : Flow_Id      renames FA.PDG.Get_Key (V);
            A_Final : V_Attributes renames FA.Atr (V);

            Written : Boolean;

         begin
            if F_Final.Variant = Final_Value
              and then A_Final.Is_Export
              and then not Synthetic (F_Final)
            then

               --  We have a final use vertex which is an export that has
               --  a single in-link. If this in-link is its initial value
               --  then clearly we do not set this output on any path.

               Written := True;
               if FA.PDG.In_Neighbour_Count (V) = 1 then
                  declare
                     V_Parent : constant Flow_Graphs.Vertex_Id :=
                       FA.PDG.Parent (V);

                     F_Parent : Flow_Id      renames FA.PDG.Get_Key (V_Parent);
                     A_Parent : V_Attributes renames FA.Atr (V_Parent);

                  begin
                     if F_Parent.Variant = Initial_Value
                       and then A_Parent.Is_Import
                       and then
                         Change_Variant (F_Parent, Final_Value) = F_Final
                     then
                        Written := False;
                     end if;
                  end;
               end if;

               if Written then
                  if A_Final.Is_Global
                    and then not FA.Is_Generative
                  then
                     declare
                        Repr : constant Entity_Id :=
                          Find_In (Unwritten_Global_Exports,
                                   Get_Direct_Mapping_Id (F_Final));

                     begin
                        if Present (Repr) then
                           Unwritten_Global_Exports.Delete (Repr);
                        end if;
                     end;
                  else
                     Written_Exports.Include (Entire_Variable (F_Final));
                  end if;
               else
                  Unwritten_Vars.Insert (V);
               end if;
            end if;
         end;
      end loop;

      for V of Unwritten_Vars loop
         declare
            F_Final : Flow_Id      renames FA.PDG.Get_Key (V);
            A_Final : V_Attributes renames FA.Atr (V);

         begin
            if A_Final.Is_Global then
               if FA.Is_Generative then
                  if not Written_Exports.Contains (Entire_Variable (F_Final))
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& is not modified, could be INPUT",
                        N        => Find_Global (FA.Spec_Entity, F_Final),
                        F1       => Entire_Variable (F_Final),
                        Tag      => Inout_Only_Read,
                        Severity => Warning_Kind,
                        Vertex   => V);
                  end if;
               else
                  if Present (Find_In (Unwritten_Global_Exports,
                                       Get_Direct_Mapping_Id (F_Final)))
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& is not modified, could be INPUT",
                        N        => Find_Global (FA.Spec_Entity, F_Final),
                        F1       => Entire_Variable (F_Final),
                        Tag      => Inout_Only_Read,
                        Severity => Warning_Kind,
                        Vertex   => V);
                  end if;
               end if;
            else
               --  We inhibit messages for non-global exports that:
               --    * have been marked as unmodified, as unused or as
               --      unreferenced,
               --    * are/belong to a concurrent object
               --    * are formal parameters of a subprogram with null default
               --      defined in the formal part of a generic unit.
               if F_Final.Kind in Direct_Mapping | Record_Field
                 and then (Has_Pragma_Un (Get_Direct_Mapping_Id (F_Final))
                             or else
                           Is_Or_Belongs_To_Concurrent_Object (F_Final)
                             or else
                           Is_Param_Of_Null_Subp_Of_Generic
                             (Get_Direct_Mapping_Id (F_Final))
                             or else
                           Is_In_Access_Parameter
                             (Get_Direct_Mapping_Id (F_Final)))
               then
                  null;
               elsif not Written_Exports.Contains (Entire_Variable (F_Final))
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& is not modified, could be IN",
                     N        => Error_Location (FA.PDG, FA.Atr, V),
                     F1       => Entire_Variable (F_Final),
                     Tag      => Inout_Only_Read,
                     Severity => Warning_Kind,
                     Vertex   => V);
               end if;
            end if;
         end;

      end loop;
   end Find_Unwritten_Exports;

   -------------------------------------------------
   -- Find_Ineffective_Imports_And_Unused_Objects --
   -------------------------------------------------

   procedure Find_Ineffective_Imports_And_Unused_Objects
     (FA : in out Flow_Analysis_Graphs)
   is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex, branches to
      --  exceptional path or is useful for proof.

      function Components_Are_Entire_Variables (Set : Flow_Id_Sets.Set)
                                                return Boolean
      with Ghost;

      procedure Collect_Imports_And_Objects
        (Suppressed         : out Flow_Id_Sets.Set;
         Considered_Imports : out Flow_Id_Sets.Set;
         Considered_Objects : out Flow_Id_Sets.Set;
         Used               : out Flow_Id_Sets.Set;
         Effective          : out Flow_Id_Sets.Set)
      with Post =>
          Components_Are_Entire_Variables (Suppressed)
          and then Components_Are_Entire_Variables (Considered_Objects)
          and then Components_Are_Entire_Variables (Considered_Imports)
          and then Components_Are_Entire_Variables (Used)
          and then Components_Are_Entire_Variables (Effective)
          and then Effective.Is_Subset (Of_Set => Considered_Imports)
          and then Used.Is_Subset (Of_Set => Considered_Objects);
      --  Collect objects and imports that we need for the analysis. The
      --  parameters have the following meanings:
      --  * Suppressed will contain entire variables appearing in a
      --    "null => Blah" dependency relation and variables that are read in a
      --    type declaration; for these we suppress the ineffective import and
      --    unused object warnings.
      --  * Considered_Imports and Considered_Objects will contain entire
      --    variables considered for each of the two analysis.
      --  * Used will contain entire variables used at least once (even if this
      --    use is not effective).
      --  * Effective will containt entire variables whose at least part is
      --    used (for example an individual component of a record, or the
      --    bounds of an unconstrained array) to determine the final value of
      --    at least one export.

      procedure Warn_On_Unused_Objects
        (Unused         : Flow_Id_Sets.Set;
         Unused_Globals : Node_Sets.Set)
      with Pre => (if FA.Is_Generative then Unused_Globals.Is_Empty);
      --  Issue a warning on unused objects; the second parameter controls
      --  emitting messages on globals coming from a user-written contract.

      procedure Warn_On_Ineffective_Imports
        (Ineffective         : Flow_Id_Sets.Set;
         Ineffective_Globals : Node_Sets.Set)
      with Pre => (if FA.Is_Generative then Ineffective_Globals.Is_Empty);
      --  Issue a warning on ineffective imports; the second parameter controls
      --  emitting messages on globals coming from a user-written contract.

      -------------------------------------
      -- Components_Are_Entire_Variables --
      -------------------------------------

      function Components_Are_Entire_Variables (Set : Flow_Id_Sets.Set)
                                                return Boolean
      is
         (for all Component of Set => Is_Entire_Variable (Component));

      ------------------
      -- Is_Final_Use --
      ------------------

      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean is
         Atr : V_Attributes renames FA.Atr (V);

      begin
         return
           (case FA.PDG.Get_Key (V).Variant is
                when Final_Value => Atr.Is_Export,
                when Normal_Use  => Atr.Is_Exceptional_Branch
                                      or else
                                    Atr.Is_Assertion,
                when others      => False);
      end Is_Final_Use;

      ---------------------------------
      -- Collect_Imports_And_Objects --
      ---------------------------------

      procedure Collect_Imports_And_Objects
        (Suppressed         : out Flow_Id_Sets.Set;
         Considered_Imports : out Flow_Id_Sets.Set;
         Considered_Objects : out Flow_Id_Sets.Set;
         Used               : out Flow_Id_Sets.Set;
         Effective          : out Flow_Id_Sets.Set)
      is
      begin
         --  Initialize sets
         Suppressed         := Flow_Id_Sets.Empty_Set;
         Considered_Imports := Flow_Id_Sets.Empty_Set;
         Considered_Objects := Flow_Id_Sets.Empty_Set;
         Used               := Flow_Id_Sets.Empty_Set;
         Effective          := Flow_Id_Sets.Empty_Set;

         if FA.Kind = Kind_Subprogram
           and then Present (FA.Depends_N)
         then

            --  We look at the null depends (if one exists). For any variables
            --  mentioned there, we suppress the ineffective import and unused
            --  object warnings by putting them to Suppressed.

            declare
               Dependency_Map : Dependency_Maps.Map;
               Null_Position  : Dependency_Maps.Cursor;

            begin
               Get_Depends (Subprogram => FA.Analyzed_Entity,
                            Scope      => FA.B_Scope,
                            Classwide  => False,
                            Depends    => Dependency_Map);

               Null_Position := Dependency_Map.Find (Null_Flow_Id);

               if Dependency_Maps.Has_Element (Null_Position) then
                  Flow_Id_Sets.Move (Target => Suppressed,
                                     Source => Dependency_Map (Null_Position));
               end if;
            end;
         end if;

         --  Detect imports that do not contribute to at least one export and
         --  objects that are never used.

         pragma Assert_And_Cut (Considered_Imports.Is_Empty and then
                                Considered_Objects.Is_Empty and then
                                Used.Is_Empty               and then
                                Effective.Is_Empty);

         for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Var : Flow_Id      renames FA.PDG.Get_Key (V);
               Atr : V_Attributes renames FA.Atr (V);

            begin
               Suppressed.Union (To_Entire_Variables (Atr.Variables_Read));

               if Var.Variant = Initial_Value
                 and then not Synthetic (Var)
               then
                  declare
                     Entire_Var : constant Flow_Id :=
                       Change_Variant (Entire_Variable (Var), Normal_Use);
                     --  The entire variable

                     Bound_Or_Discr : constant Boolean :=
                       Is_Bound (Var) or else Is_Discriminant (Var);
                     --  If this is an array bound or a discriminant, we only
                     --  consider it if it is actually used. It is OK to not
                     --  explicitly use it.

                  begin
                     --  Using bounds or discriminants marks the entire
                     --  variable as used; not using them has no effect.
                     --  However, this only applies to out parameters; for in
                     --  out parameters the value of the entire variable itself
                     --  has to be used and uses of bounds and discriminants
                     --  are completely ignored.

                     if Bound_Or_Discr
                       and then Atr.Mode = Mode_In_Out
                     then
                        null;
                     else
                        --  Determine effective and considered imports

                        if Atr.Is_Initialized and Atr.Is_Import then

                           --  Check if we're effective. If not, note that we
                           --  at least partially have used the entire
                           --  variable.

                           if FA.PDG.Non_Trivial_Path_Exists
                             (V, Is_Final_Use'Access)
                           then
                              Considered_Imports.Include (Entire_Var);
                              Effective.Include (Entire_Var);
                           else
                              if not Bound_Or_Discr then
                                 Considered_Imports.Include (Entire_Var);
                              end if;
                           end if;
                        end if;

                        --  Determine used and considered objects

                        if FA.PDG.Out_Neighbour_Count (V) = 1 then
                           declare
                              Final_V : constant Flow_Graphs.Vertex_Id :=
                                FA.PDG.Child (V);
                           begin
                              if FA.PDG.Get_Key (Final_V).Variant /=
                                   Final_Value
                                or else
                                  FA.PDG.In_Neighbour_Count (Final_V) > 1
                              then
                                 Considered_Objects.Include (Entire_Var);
                                 Used.Include (Entire_Var);
                              else
                                 if not Bound_Or_Discr then
                                    Considered_Objects.Include (Entire_Var);
                                 end if;
                              end if;
                           end;
                        else
                           Considered_Objects.Include (Entire_Var);
                           Used.Include (Entire_Var);
                        end if;
                     end if;
                  end;
               end if;
            end;
         end loop;
      end Collect_Imports_And_Objects;

      ----------------------------
      -- Warn_On_Unused_Objects --
      ----------------------------

      procedure Warn_On_Unused_Objects
        (Unused         : Flow_Id_Sets.Set;
         Unused_Globals : Node_Sets.Set)
      is
      begin
         for F of Unused loop
            declare
               V : constant Flow_Graphs.Vertex_Id :=
                 Get_Initial_Vertex (FA.PDG, F);

            begin
               if FA.Atr (V).Is_Global then
                  --  In generative mode we inhibit messages on globals
                  if not FA.Is_Generative then
                     declare
                        Repr : constant Entity_Id :=
                          Find_In (Unused_Globals, Get_Direct_Mapping_Id (F));
                        --  An entity that represents F in unused, user-written
                        --  Global/Depends items.

                        Is_Var : constant Boolean := Is_Variable (F);
                        --  Issue a different errors for variables and
                        --  constants

                        Msg : constant String :=
                          (if Is_Var
                           then "unused global &"
                           else "& cannot appear in Globals");

                        Severity : constant Msg_Severity :=
                          (if Is_Var
                           then Low_Check_Kind
                           else Medium_Check_Kind);

                     begin
                        --  We prefer the report the error on the subprogram,
                        --  not on the global.

                        if Present (Repr) then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => Msg,
                              N        =>
                                Find_Global
                                  (FA.Spec_Entity,
                                   Direct_Mapping_Id (Repr)),
                              F1       => Direct_Mapping_Id (Repr),
                              Tag      => VC_Kinds.Unused,
                              Severity => Severity,
                              Vertex   => V);
                        end if;
                     end;
                  end if;
               else
                  --  We suppress this warning when:
                  --  * we are dealing with a concurrent type or a component of
                  --    a concurrent type
                  --  * we are dealing with a null record
                  --  * the variable has been marked either as Unreferenced or
                  --    Unmodified or Unused
                  --  * the variable is a formal parameter of a null subprogram
                  --    of a generic unit.
                  declare
                     E     : constant Entity_Id := Get_Direct_Mapping_Id (F);
                     E_Typ : constant Entity_Id := Etype (E);

                     Msg : constant String :=
                       (if Ekind (Scope (E)) = E_Function
                        and then Is_Predicate_Function (Scope (E))
                        then "& is not used in its predicate"
                        else "unused variable &");

                  begin
                     if Is_Concurrent_Type (E_Typ)
                       or else Is_Empty_Record_Type (E_Typ)
                       or else Has_Pragma_Un (E)
                       or else Has_Junk_Name (E)
                       or else Is_Param_Of_Null_Subp_Of_Generic (E)
                     then
                        null;

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => Msg,
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           F1       => F,
                           Tag      => VC_Kinds.Unused,
                           Severity => Warning_Kind);
                     end if;
                  end;
               end if;
            end;
         end loop;
      end Warn_On_Unused_Objects;

      ---------------------------------
      -- Warn_On_Ineffective_Imports --
      ---------------------------------

      procedure Warn_On_Ineffective_Imports
        (Ineffective         : Flow_Id_Sets.Set;
         Ineffective_Globals : Node_Sets.Set)
      is
      begin
         for F of Ineffective loop
            declare
               V   : constant Flow_Graphs.Vertex_Id :=
                 Get_Initial_Vertex (FA.PDG, F);
               Atr : V_Attributes renames FA.Atr (V);

            begin
               if F.Kind = Direct_Mapping
                 and then (Has_Pragma_Un (Get_Direct_Mapping_Id (F))
                           or else
                             (In_Generic_Actual (Get_Direct_Mapping_Id (F))
                              and then
                              Scope_Within_Or_Same
                                (Scope (Get_Direct_Mapping_Id (F)),
                                 FA.Spec_Entity)))
               then
                  --  This variable is marked with a pragma Unreferenced,
                  --  pragma Unused or pragma Unmodified so we do not warn
                  --  here; also, we do not warn for ineffective declarations
                  --  of constants in wrapper packages of generic subprograms.
                  --  ??? maybe we want a separate check for them.
                  null;
               elsif Atr.Is_Global then
                  if FA.Kind = Kind_Subprogram
                    and then not FA.Is_Generative
                    and then Present (Find_In (Ineffective_Globals,
                                               Get_Direct_Mapping_Id (F)))
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "unused initial value of &",
                        N        => Find_Global (FA.Spec_Entity, F),
                        F1       => F,
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Unused_Initial_Value,
                        Severity => Warning_Kind,
                        Vertex   => V);
                  end if;
               else
                  --  We suppress this warning when we are dealing with a
                  --  concurrent type or a component of a concurrent type or a
                  --  null record.
                  if F.Kind = Direct_Mapping
                    and then
                      (Is_Concurrent_Type (Get_Direct_Mapping_Id (F))
                         or else
                       Is_Empty_Record_Type
                         (Etype (Get_Direct_Mapping_Id (F))))
                  then
                     null;

                  else
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "unused initial value of &",
                        --  ??? find_import
                        N        => Error_Location (FA.PDG, FA.Atr, V),
                        F1       => F,
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Unused_Initial_Value,
                        Severity => Warning_Kind,
                        Vertex   => V);
                  end if;
               end if;
            end;
         end loop;
      end Warn_On_Ineffective_Imports;

   --  Start of processing for Find_Ineffective_Imports_And_Unused_Objects

   begin
      --  If this subprogram has only exceptional paths, then we already have a
      --  high check for this. We don't issue any other messages as they
      --  distract from the real issue.

      if FA.Has_Only_Exceptional_Paths then
         return;
      end if;

      --  If this subprogram has effects or is annotated with globals by the
      --  user then we continue the analysis.

      if Has_Effects (FA)
        or else Has_User_Supplied_Globals (FA.Analyzed_Entity)
      then
         declare
            Suppressed         : Flow_Id_Sets.Set;
            Considered_Imports : Flow_Id_Sets.Set;
            Considered_Objects : Flow_Id_Sets.Set;
            Used               : Flow_Id_Sets.Set;
            Effective          : Flow_Id_Sets.Set;

            Unused             : Flow_Id_Sets.Set;

            Raw_Globals        : Raw_Global_Nodes;

            use type Node_Sets.Set;

            Unused_Global_Objects      : Node_Sets.Set;
            Ineffective_Global_Imports : Node_Sets.Set;

         begin
            Collect_Imports_And_Objects (Suppressed,
                                         Considered_Imports,
                                         Considered_Objects,
                                         Used,
                                         Effective);

            if not FA.Is_Generative then
               Raw_Globals := Contract_Globals (FA.Spec_Entity);

               Unused_Global_Objects :=
                 Raw_Globals.Proof_Ins
                 or Raw_Globals.Inputs
                 or Raw_Globals.Outputs;
               --  ??? adding Outputs is wrong, but minimizes diffs with the
               --  old Is_Visible.

               for U of Used loop
                  if U.Kind = Direct_Mapping then
                     declare
                        Repr : constant Entity_Id :=
                          Find_In (Unused_Global_Objects,
                                   Get_Direct_Mapping_Id (U));
                        --  An entity that represents U in the user-written
                        --  Global/Depends contract.

                     begin
                        if Present (Repr) then
                           Unused_Global_Objects.Delete (Repr);
                        end if;
                     end;
                  end if;
               end loop;

               Suppressed := Suppressed -
                 To_Flow_Id_Set (Unused_Global_Objects);

               Ineffective_Global_Imports :=
                 Raw_Globals.Proof_Ins
                 or Raw_Globals.Inputs
                 or Raw_Globals.Outputs;
               --  ??? adding Outputs is wrong, but minimizes diffs with the
               --  old Is_Visible.

               for U of Effective loop
                  if U.Kind = Direct_Mapping then
                     declare
                        Repr : constant Entity_Id :=
                          Find_In (Ineffective_Global_Imports,
                                   Get_Direct_Mapping_Id (U));
                        --  An entity that represents U in the user-written
                        --  Global/Depends contract.

                     begin
                        if Present (Repr) then
                           Ineffective_Global_Imports.Delete (Repr);
                        end if;
                     end;
                  end if;
               end loop;
            end if;

            --  We warn on unused objects. From all the imports we exclude
            --  items which are suppressed by a null dependency,
            Unused := Considered_Objects - (Used or Suppressed);

            Warn_On_Unused_Objects (Unused, Unused_Global_Objects);

            --  If this subprogram has effects then we also want to find
            --  ineffective imports.

            if Has_Effects (FA) then
               --  We warn on ineffective imports. From all the imports we
               --  exclude items which are suppressed by a null dependency,
               --  which have been flagged as unused and which are effective
               --  imports.

               Warn_On_Ineffective_Imports
                 (Considered_Imports - (Effective or Suppressed or Unused),
                  Ineffective_Global_Imports);
            end if;
         end;

      elsif not Has_Effects (FA) then
         Warn_On_Subprogram_With_No_Effect (FA);
      end if;
   end Find_Ineffective_Imports_And_Unused_Objects;

   --------------------------------------------
   -- Find_Non_Elaborated_State_Abstractions --
   --------------------------------------------

   procedure Find_Non_Elaborated_State_Abstractions
     (FA : in out Flow_Analysis_Graphs)
   is
      procedure Check_If_From_Another_Non_Elaborated_CU
        (F : Flow_Id;
         V : Flow_Graphs.Vertex_Id)
      with Pre => F.Variant = Initial_Value;
      --  If F is used but is not declared in the compilation unit enclosing
      --  the currently analyzed entity AND the other compilation unit does not
      --  have an Elaborate[_All] then emit an error.

      ---------------------------------------------
      -- Check_If_From_Another_Non_Elaborated_CU --
      ---------------------------------------------

      procedure Check_If_From_Another_Non_Elaborated_CU
        (F : Flow_Id;
         V : Flow_Graphs.Vertex_Id)
      is

         E : constant Entity_Id := (if F.Kind = Direct_Mapping
                                    then Get_Direct_Mapping_Id (F)
                                    else Empty);

         pragma Assert (if Present (E) then Ekind (E) = E_Abstract_State);

         V_Use : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

         V_Error_Location : Node_Or_Entity_Id;

      --  Start of processing for Check_If_From_Another_Non_Elaborated_CU

      begin
         --  Find a non-'Final vertex where the state abstraction is used. If
         --  the state abstraction is not used then we do not issue an error.
         --  ??? this search is useful only when Present (N)
         for Neighbour of FA.PDG.Get_Collection (V, Flow_Graphs.Out_Neighbours)
         loop
            declare
               Key : Flow_Id renames FA.PDG.Get_Key (Neighbour);
            begin
               if Key.Variant /= Final_Value
                 or else
                   Change_Variant (Key, Initial_Value) /= F
               then
                  V_Use := Neighbour;
                  V_Error_Location := FA.Atr (Neighbour).Error_Location;
                  exit;
               end if;
            end;
         end loop;

         if Present (E)
           and then V_Use /= Flow_Graphs.Null_Vertex
           and then Is_Compilation_Unit (Scope (E))
           and then Scope (E) /= FA.Spec_Entity
         then
            declare
               Current_Unit : constant Node_Id :=
                 Enclosing_Comp_Unit_Node (FA.Spec_Entity);
               Other_Unit   : constant Node_Id :=
                 Enclosing_Comp_Unit_Node (Scope (E));

               Found        : Boolean := False;
               --  Found will become True if we find a pragma Elaborate[_All]
               --  for Other_Unit. We initialy set it to False.

               procedure Check_Clauses (CUnit : Node_Id);
               --  Checks the clauses of CUnit for a pragma Elaborate[_All] of
               --  Other_Unit and sets Found to True if it finds it.

               -------------------
               -- Check_Clauses --
               -------------------

               procedure Check_Clauses (CUnit : Node_Id) is
                  Clause : Node_Id := First (Context_Items (CUnit));
               begin
                  while Present (Clause) loop
                     if Nkind (Clause) = N_With_Clause
                       and then Library_Unit (Clause) = Other_Unit
                       and then (Elaborate_All_Present (Clause)
                                   or else Elaborate_Present (Clause))
                     then
                        Found := True;
                        return;
                     end if;

                     Next (Clause);
                  end loop;
               end Check_Clauses;

            begin
               --  Check clauses of the spec
               Check_Clauses (Current_Unit);

               --  Check also clauses of the body
               if not Found
                 and then FA.Analyzed_Entity /= FA.Spec_Entity
               then
                  Check_Clauses
                    (Enclosing_Comp_Unit_Node (FA.Analyzed_Entity));
               end if;

               if not Found then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "use of remote abstract state &" &
                                 " during elaboration of &" &
                                 " - Elaborate pragma required for &",
                     SRM_Ref  => "7.7.1(4)",
                     N        => V_Error_Location,
                     F1       => F,
                     F2       => Direct_Mapping_Id (FA.Spec_Entity),
                     F3       => Direct_Mapping_Id (Scope (E)),
                     Severity => Medium_Check_Kind,
                     Tag      => Pragma_Elaborate_All_Needed);
               end if;
            end;
         end if;
      end Check_If_From_Another_Non_Elaborated_CU;

   --  Start of processing for Find_Non_Elaborated_State_Abstractions

   begin
      --  If we are not analyzing a compilation unit then there is
      --  nothing to do here.
      if not Is_Compilation_Unit (FA.Analyzed_Entity) then
         return;
      end if;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F : Flow_Id renames FA.PDG.Get_Key (V);
         begin
            if F.Variant = Initial_Value
              and then Is_Abstract_State (F)
            then
               Check_If_From_Another_Non_Elaborated_CU (F, V);
            end if;
         end;
      end loop;
   end Find_Non_Elaborated_State_Abstractions;

   ---------------------------------
   -- Find_Ineffective_Statements --
   ---------------------------------

   procedure Find_Ineffective_Statements (FA : in out Flow_Analysis_Graphs) is

      function Defines_Async_Reader_Var
        (V : Flow_Graphs.Vertex_Id)
         return Boolean;
      --  Returns True if vertex V defines some variable that has property
      --  Async_Readers set.

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set;
      --  Find out why a given vertex is ineffective. A vertex is ineffective
      --  if the variable(s) defined by it are re-defined on all paths leading
      --  from it without being used. Thus all reachable vertices which also
      --  define at least one variable of that set (and do not use it), render
      --  the vertex ineffective.

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if from the given vertex V it is impossible to reach the end
      --  vertex.

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean;
      --  Checks if the given vertex V represents an externally visible
      --  outcome, i.e. is a final-use vertex that is also an export or a use
      --  vertex that branches to an exceptional path.
      --  ??? same as Find_Ineffective_Imports_And_Unused_Objects.Is_Final_Use

      function Is_In_Pragma_Un (S : Flow_Id_Sets.Set)
                                return Boolean;
      --  Checks if variables in the set Variables_Defined have been mentioned
      --  in a pragma Unmodified, Unused or Unreferenced.

      function Is_Package_Elaboration (V : Flow_Graphs.Vertex_Id)
                                       return Boolean;
      --  Checks if V represents elaboration of a nested package

      function Other_Fields_Are_Ineffective (V : Flow_Graphs.Vertex_Id)
                                             return Boolean;
      --  This function returns True if V corresponds to an assignment to a
      --  record field that has been introduced by a record split and the rest
      --  of the fields are ineffective.

      function Skip_Any_Conversions (N : Node_Id) return Node_Id
      with Pre  => Nkind (N) in N_Subexpr,
           Post => Nkind (Skip_Any_Conversions'Result) in N_Subexpr;
      --  Skips any conversions (unchecked or otherwise) and jumps to the
      --  actual object.
      --  ??? this routine actually skips only checked conversion; to have what
      --  this comment says we can reuse Sem_Util.Unqual_Conv.

      ------------------------------
      -- Defines_Async_Reader_Var --
      ------------------------------

      function Defines_Async_Reader_Var
        (V : Flow_Graphs.Vertex_Id)
         return Boolean
      is
        (for some Var_Def of FA.Atr (V).Variables_Defined =>
           Has_Async_Readers (Var_Def));

      -----------------------
      -- Find_Masking_Code --
      -----------------------

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set
      is
         Mask         : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
         Vars_Defined : Flow_Id_Sets.Set renames
           FA.Atr (Ineffective_Statement).Variables_Defined;

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Check if V masks the ineffective statement

         -------------
         -- Visitor --
         -------------

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
         begin
            if V = Ineffective_Statement then
               TV := Flow_Graphs.Continue;
            else
               declare
                  Intersection : constant Flow_Id_Sets.Set :=
                    Vars_Defined and
                    (FA.Atr (V).Variables_Defined - FA.Atr (V).Variables_Used);

               begin
                  if Intersection.Is_Empty then
                     TV := Flow_Graphs.Continue;
                  else
                     Mask.Insert (V);
                     TV := Flow_Graphs.Skip_Children;
                  end if;
               end;
            end if;
         end Visitor;

      --  Start of processing for Find_Masking_Code

      begin
         FA.CFG.DFS (Start         => Ineffective_Statement,
                     Include_Start => False,
                     Visitor       => Visitor'Access);
         return Mask;
      end Find_Masking_Code;

      ----------------------
      -- Is_Any_Final_Use --
      ----------------------

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id)
                                 return Boolean
      is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value;
      end Is_Any_Final_Use;

      -----------------
      -- Is_Dead_End --
      -----------------

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id) return Boolean is
         Dead_End : Boolean := True;

         procedure Visitor (V  : Flow_Graphs.Vertex_Id;
                            TV : out Flow_Graphs.Simple_Traversal_Instruction);

         -------------
         -- Visitor --
         -------------

         procedure Visitor (V  : Flow_Graphs.Vertex_Id;
                            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
         begin
            if FA.Atr (V).Execution /= Normal_Execution then
               TV := Flow_Graphs.Skip_Children;
            elsif V = FA.Helper_End_Vertex then
               Dead_End := False;
               TV := Flow_Graphs.Abort_Traversal;
            else
               TV := Flow_Graphs.Continue;
            end if;
         end Visitor;

      --  Start of processing for Is_Dead_End

      begin
         FA.CFG.DFS (Start         => V,
                     Include_Start => True,
                     Visitor       => Visitor'Access);
         return Dead_End or else
           not FA.CFG.Non_Trivial_Path_Exists (FA.Start_Vertex, V);
      end Is_Dead_End;

      -----------------------------
      -- Is_Final_Use_Any_Export --
      -----------------------------

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean
      is
        (case FA.PDG.Get_Key (V).Variant is
            when Final_Value => FA.Atr (V).Is_Export,
            when Normal_Use  => FA.Atr (V).Is_Exceptional_Branch
                                  or else
                                FA.Atr (V).Is_Assertion,
            when others      => False);

      ---------------------
      -- Is_In_Pragma_Un --
      ---------------------

      function Is_In_Pragma_Un (S : Flow_Id_Sets.Set)
                                return Boolean
      is
        (for some F of S =>
           F.Kind in Direct_Mapping | Record_Field
             and then (Has_Pragma_Un (Get_Direct_Mapping_Id (F))
                         or else
                       Has_Junk_Name (Get_Direct_Mapping_Id (F))));

      ----------------------------
      -- Is_Package_Elaboration --
      ----------------------------

      function Is_Package_Elaboration (V : Flow_Graphs.Vertex_Id)
                                       return Boolean
      is
         F : constant Flow_Id := FA.CFG.Get_Key (V);
      begin
         --  Match attributes of vertices created in Do_Package_Declaration

         return F.Kind = Direct_Mapping
           and then Nkind (Get_Direct_Mapping_Id (F)) = N_Package_Declaration;
      end Is_Package_Elaboration;

      --------------------------
      -- Skip_Any_Conversions --
      --------------------------

      function Skip_Any_Conversions (N : Node_Id) return Node_Id is
         P : Node_Id := N;
      begin
         loop
            case Nkind (P) is
               when N_Type_Conversion =>
                  P := Expression (P);

               when others =>
                  return P;
            end case;
         end loop;
      end Skip_Any_Conversions;

      ----------------------------------
      -- Other_Fields_Are_Ineffective --
      ----------------------------------

      function Other_Fields_Are_Ineffective (V : Flow_Graphs.Vertex_Id)
                                             return Boolean
      is
      begin
         if FA.Other_Fields.Contains (V) then
            for Other_Field of FA.Other_Fields (V) loop
               if FA.PDG.Non_Trivial_Path_Exists
                 (Other_Field, Is_Final_Use_Any_Export'Access)
               then
                  return False;
               end if;
            end loop;
         end if;

         --  If we reach this point then all other fields are ineffective

         return True;
      end Other_Fields_Are_Ineffective;

   --  Start of processing for Find_Ineffective_Statements

   begin
      if FA.Kind = Kind_Subprogram
        and then not Has_Effects (FA)
      then
         Warn_On_Subprogram_With_No_Effect (FA);
         return;
      end if;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : Flow_Id renames FA.PDG.Get_Key (V);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Atr.Is_Program_Node
              or Atr.Is_Parameter
              or Atr.Is_Global_Parameter
            then

               --  A vertex is ineffective if there is no path in the PDG to
               --  *any* final use vertex that is also an export.

               if
                 --  Basic check here
                 not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use_Any_Export'Access) and then

                 --  Suppression for dead code
                 not Is_Dead_End (V) and then

                 --  Suppression for package initializations
                 not Atr.Is_Package_Initialization and then

                 --  If we analyse a package, we suppress this message if we
                 --  don't have an initializes clause *and* the given vertex
                 --  has an effect on any final use (export or otherwise).
                 (if FA.Kind in Kind_Package | Kind_Package_Body
                    and then No (FA.Initializes_N)
                  then
                     not FA.PDG.Non_Trivial_Path_Exists
                      (V, Is_Any_Final_Use'Access)) and then

                 --  Suppression for vertices that talk about a variable that
                 --  is mentioned in a pragma Unused, Unmodified or
                 --  Unreferenced.
                 not Is_In_Pragma_Un (Atr.Variables_Defined) and then

                 --  Suppression for vertices that can lead to abnormal
                 --  termination and have had some of their out edges removed.
                 not Atr.Is_Exceptional_Branch and then

                 --  Suppression for vertices that correspond to an assignment
                 --  to a record field, that comes from a record split, while
                 --  the rest of the fields are not ineffective.
                 Other_Fields_Are_Ineffective (V) and then

                 --  Suppression for vertices that define a variable that has
                 --  Async_Readers set.
                 not Defines_Async_Reader_Var (V) and then

                 --  Suppression for elaboration of nested packages
                 not Is_Package_Elaboration (V)

               then
                  declare
                     Mask : constant Vertex_Sets.Set := Find_Masking_Code (V);
                     N    : constant Node_Id := Error_Location (FA.PDG,
                                                                FA.Atr,
                                                                V);

                  begin
                     if Atr.Is_Parameter or Atr.Is_Global_Parameter then

                        --  Suppress error messages for:
                        --  * IN parameters
                        --  * IN views of globals
                        --  * discriminants and bounds of parameters

                        if (Atr.Is_Parameter
                            and then Key.Variant = In_View)
                          or else
                            (Atr.Is_Global_Parameter
                             and then Atr.Parameter_Formal.Variant = In_View)
                          or else
                            Atr.Is_Discr_Or_Bounds_Parameter
                          or else
                            Is_Bound (Key)
                        then
                           null;

                        else
                           declare
                              Target : constant Flow_Id :=
                                (if Atr.Is_Parameter
                                 then Direct_Mapping_Id
                                   (Skip_Any_Conversions
                                      (Get_Direct_Mapping_Id
                                         (Atr.Parameter_Actual)))
                                 else Atr.Parameter_Formal);

                              Printable_Target : constant Boolean :=
                                Is_Easily_Printable (Target);

                           begin
                              Error_Msg_Flow
                                (FA       => FA,
                                 Path     => Mask,
                                 Msg      => (if Printable_Target
                                              then "unused assignment to &"
                                              else "unused assignment"),
                                 N        => N,
                                 F1       => (if Printable_Target
                                              then Target
                                              else Null_Flow_Id),
                                 Tag      => Ineffective,
                                 Severity => Warning_Kind,
                                 Vertex   => V);
                           end;
                        end if;

                     elsif Nkind (N) = N_Assignment_Statement then
                        Error_Msg_Flow
                          (FA       => FA,
                           Path     => Mask,
                           Msg      => "unused assignment",
                           N        => N,
                           Tag      => Ineffective,
                           Severity => Warning_Kind,
                           Vertex   => V);

                     elsif Nkind (N) = N_Object_Declaration then
                        if not Constant_Present (N) then

                           --  This warning is ignored for local constants

                           if FA.Kind in Kind_Package | Kind_Package_Body
                             and then
                               Scope (Defining_Identifier (N)) = FA.Spec_Entity
                             and then
                                 No (Find_In_Initializes
                                       (Defining_Identifier (N)))
                           then

                              --  This is checked by Check_Initializes_Contract

                              null;

                           else
                              Error_Msg_Flow
                                (FA       => FA,
                                 Path     => Mask,
                                 Msg      => "initialization of & has no " &
                                             "effect",
                                 N        => N,
                                 F1       => Direct_Mapping_Id
                                               (Defining_Entity (N)),
                                 Tag      => Ineffective,
                                 Severity => Warning_Kind,
                                 Vertex   => V);
                           end if;

                        end if;

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Path     => Mask,
                           Msg      => "statement has no effect",
                           Severity => Warning_Kind,
                           N        => N,
                           Tag      => Ineffective,
                           Vertex   => V);
                     end if;
                  end;
               end if;
            end if;
         end;
      end loop;
   end Find_Ineffective_Statements;

   --------------------
   -- Find_Dead_Code --
   --------------------

   procedure Find_Dead_Code (FA : in out Flow_Analysis_Graphs) is
      Dead_Code : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Flag the given node as "live"

      ---------------
      -- Flag_Live --
      ---------------

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
      begin
         Dead_Code.Exclude (V);
         TV := (if FA.Atr (V).Execution = Barrier
                then Flow_Graphs.Skip_Children
                else Flow_Graphs.Continue);
      end Flag_Live;

   --  Start of processing for Find_Dead_Code

   begin
      --  Guilty until proven innocent
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
         begin
            if Atr.Is_Program_Node then
               Dead_Code.Insert (V);
            end if;
         end;
      end loop;

      --  Discover live code
      FA.CFG.DFS (Start         => FA.Start_Vertex,
                  Include_Start => True,
                  Visitor       => Flag_Live'Access);

      --  Anything remaining is dead
      for V of Dead_Code loop
         Error_Msg_Flow (FA       => FA,
                         Msg      => "this statement is never reached",
                         Severity => Warning_Kind,
                         N        => FA.Atr (V).Error_Location,
                         Tag      => VC_Kinds.Dead_Code,
                         Vertex   => V);
      end loop;
   end Find_Dead_Code;

   -----------------------------------------
   -- Find_Use_Of_Uninitialized_Variables --
   -----------------------------------------

   procedure Find_Use_Of_Uninitialized_Variables
     (FA : in out Flow_Analysis_Graphs)
   is
      type Msg_Kind is (Unknown, Err);

      procedure Emit_Check_Message
        (Var   : Flow_Id;
         V_Use : Flow_Graphs.Vertex_Id;
         Kind  : Msg_Kind;
         OK    : in out Boolean)
      with Pre  => not Is_Internal (Var)
                   and then V_Use /= Flow_Graphs.Null_Vertex,
           Post => not OK;
      --  Produces an appropriately worded low/high message for variable Var
      --  when used at Vertex.

      procedure Emit_Info_Message_Global (Var : Flow_Id)
      with Pre => Var.Kind in Direct_Mapping | Magic_String;

      procedure Emit_Info_Message_Local (Var : Flow_Id)
      with Pre => Var.Kind = Direct_Mapping;
      --  Emit an appropriately worded info message for variable Var; messages
      --  for global and local variables look the same, bug have different
      --  locations.

      function Might_Be_Initialized
        (Var       : Flow_Id;
         V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id)
         return Boolean
      with Pre => Var.Variant = Normal_Use and then not Synthetic (Var);
      --  Returns True if Var, when accessed as uninitialized in V_Use,
      --  might be in fact initialized; returns False if it is definitely
      --  uninitialized there.

      function Has_Only_Infinite_Execution (V_Final : Flow_Graphs.Vertex_Id)
                                            return Boolean;
      pragma Unreferenced (Has_Only_Infinite_Execution);
      --  Returns True iff every path from V_Final going backwards in the CFG
      --  contains an infinite loop.

      procedure Scan_Children
        (Var                  : Flow_Id;
         Start                : Flow_Graphs.Vertex_Id;
         Possibly_Initialized : Boolean;
         Visited              : in out Vertex_Sets.Set;
         OK                   : in out Boolean)
      with Pre  => Var.Variant = Normal_Use
                   and then Start /= Flow_Graphs.Null_Vertex,
           Post => Vertex_Sets.Is_Subset (Subset => Visited'Old,
                                          Of_Set => Visited)
                   and then (if not OK'Old then not OK);
      --  Detect uses of Var, which is an not-yet-initializes object, by
      --  looking at the PDG vertices originating from Start. For arrays this
      --  routine might be called recursively and then Possibly_Initialized
      --  is True iff some elements of the array have been written. Visited
      --  contains vertices that have been already examined; it is to prevent
      --  infinite recursive calls. If any message is emitted, then OK will
      --  become False; otherwise, if will be unmodified.

      function Is_Array (F : Flow_Id) return Boolean;
      --  Returns True iff F represents an array and thus requires special
      --  handling.

      function Is_Empty_Record_Object (F : Flow_Id) return Boolean;
      --  Returns True iff F is a record that carries no data

      function Is_Init_By_Proof (F : Flow_Id) return Boolean;
      --  Returns True iff F is annotated with Has_Init_By_Proof

      ------------------------
      -- Emit_Check_Message --
      ------------------------

      procedure Emit_Check_Message
        (Var   : Flow_Id;
         V_Use : Flow_Graphs.Vertex_Id;
         Kind  : Msg_Kind;
         OK    : in out Boolean)
      is
         V_Key        : Flow_Id renames FA.PDG.Get_Key (V_Use);

         V_Initial    : constant Flow_Graphs.Vertex_Id :=
           FA.PDG.Get_Vertex (Change_Variant (Var, Initial_Value));

         N            : Node_Or_Entity_Id;
         Msg          : Unbounded_String;

         V_Goal       : Flow_Graphs.Vertex_Id;

         Is_Final_Use : constant Boolean := V_Key.Variant = Final_Value;
         Is_Global    : constant Boolean := FA.Atr (V_Initial).Is_Global;
         Default_Init : constant Boolean := Is_Default_Initialized
                                               (Var, FA.B_Scope);
         Is_Function  : constant Boolean := Is_Function_Entity (Var);

         function Mark_Definition_Free_Path
           (To  : Flow_Graphs.Vertex_Id;
            Var : Flow_Id)
            return Vertex_Sets.Set;
         --  Returns a path from Start towards To (where Var is read) that does
         --  not define Var.

         -------------------------------
         -- Mark_Definition_Free_Path --
         -------------------------------

         function Mark_Definition_Free_Path
           (To  : Flow_Graphs.Vertex_Id;
            Var : Flow_Id)
            return Vertex_Sets.Set
         is
            Path_Found : Boolean := False;
            Path       : Vertex_Sets.Set;

            procedure Are_We_There_Yet
              (V           : Flow_Graphs.Vertex_Id;
               Instruction : out Flow_Graphs.Traversal_Instruction);
            --  Visitor procedure for Shortest_Path

            procedure Add_Loc (V : Flow_Graphs.Vertex_Id);
            --  Step procedure for Shortest_Path

            ----------------------
            -- Are_We_There_Yet --
            ----------------------

            procedure Are_We_There_Yet
              (V           : Flow_Graphs.Vertex_Id;
               Instruction : out Flow_Graphs.Traversal_Instruction)
            is
            begin
               if V = To then
                  Instruction := Flow_Graphs.Found_Destination;
                  Path_Found  := True;
               elsif FA.Atr (V).Variables_Defined.Contains (Var) then
                  Instruction := Flow_Graphs.Skip_Children;
               else
                  Instruction := Flow_Graphs.Continue;
               end if;
            end Are_We_There_Yet;

            -------------
            -- Add_Loc --
            -------------

            procedure Add_Loc (V : Flow_Graphs.Vertex_Id) is
               F : Flow_Id renames FA.CFG.Get_Key (V);
            begin
               if V /= To and then F.Kind = Direct_Mapping then
                  Path.Insert (V);
               end if;
            end Add_Loc;

         --  Start of processing for Mark_Definition_Free_Path

         begin
            FA.CFG.Shortest_Path (Start         => FA.Start_Vertex,
                                  Allow_Trivial => False,
                                  Search        => Are_We_There_Yet'Access,
                                  Step          => Add_Loc'Access);

            --  When dealing with an exceptional path it is possible for
            --  Path_Found to be false.
            --  ??? this actually should work now, except for array objects
            pragma Assert (if not Path_Found then Is_Array (Var));

            return (if Path_Found
                    then Path
                    else Vertex_Sets.Empty_Set);
         end Mark_Definition_Free_Path;

      --  Start of processing for Emit_Message

      begin
         --  Assemble appropriate message for failed initialization. We deal
         --  with a bunch of special cases first, but if they don't trigger we
         --  create the standard message.

         if Is_Function then
            Msg := To_Unbounded_String ("function & does not return on ");
--              if Has_Only_Infinite_Execution (Vertex) then
--                 Append (Msg, "any path");
--              else
--                 Append (Msg, "some paths");
--              end if;
            Append (Msg, "some paths");
         else
            Msg := To_Unbounded_String ("&");
            if Kind = Err then
               Append (Msg, " is not");
            else
               Append (Msg, " might not be");
            end if;
            if Default_Init then
               Append (Msg, " set");
            elsif Has_Async_Readers (Var) then
               Append (Msg, " written");
            else
               Append (Msg, " initialized");
            end if;
            if Is_Final_Use and not Is_Global then
               Append (Msg, " in &");
            end if;
         end if;

         if not Is_Final_Use then
            V_Goal := V_Use;

            N := First_Variable_Use
              (N        => Error_Location (FA.PDG, FA.Atr, V_Use),
               Scope    => FA.B_Scope,
               Var      => Var,
               Precise  => True,
               Targeted => True);

         elsif Is_Global then
            V_Goal := FA.End_Vertex;
            N      := Find_Global (FA.Spec_Entity, Var);
         else
            V_Goal := V_Use;
            N      := FA.Atr (V_Use).Error_Location;
         end if;

         declare
            Path : constant Vertex_Sets.Set :=
              Mark_Definition_Free_Path (To  => V_Goal,
                                         Var => Var);

         begin
            Error_Msg_Flow
              (FA       => FA,
               Path     => Path,
               Msg      => To_String (Msg),
               N        => N,
               F1       => Var,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag      => Uninitialized,
               Severity => (case Kind is
                            when Unknown => (if Default_Init
                                             then Low_Check_Kind
                                             else Medium_Check_Kind),
                            when Err     => (if Default_Init
                                             then Medium_Check_Kind
                                             else High_Check_Kind)),
               Vertex   => V_Use);

            --  ??? only when Is_Final_Use ?
            if Is_Constituent (Var)
              and then FA.Kind in Kind_Package | Kind_Package_Body
              and then Present (FA.Initializes_N)
            then
               Error_Msg_Flow
                 (FA           => FA,
                  Msg          => "initialization of & is specified @",
                  N            => N,
                  F1           => Direct_Mapping_Id
                                    (Encapsulating_State
                                       (Get_Direct_Mapping_Id (Var))),
                  F2           => Direct_Mapping_Id (FA.Initializes_N),
                  Tag          => Uninitialized,
                  Severity     => (case Kind is
                                      when Unknown => Medium_Check_Kind,
                                      when Err     => High_Check_Kind),
                  Vertex       => V_Use,
                  Continuation => True);
            end if;
         end;

         --  In case of a subprogram with an output global which is actually
         --  used as an input in its body, we add more information to the error
         --  message.
         if Kind = Err
           and then not Default_Init
           and then Is_Global
         then
            Error_Msg_Flow (FA           => FA,
                            Msg          => "& is not an input " &
                              "in the Global contract of subprogram #",
                            Severity     => High_Check_Kind,
                            N            => N,
                            F1           => Var,
                            F2           =>
                              Direct_Mapping_Id (FA.Spec_Entity),
                            Tag          => Uninitialized,
                            Continuation => True);

            declare
               Msg : constant String :=
                 "either make & an input in the Global contract or " &
                 (if Has_Async_Readers (Var)
                  then "write to it before use"
                  else "initialize it before use");

            begin
               Error_Msg_Flow (FA           => FA,
                               Msg          => Msg,
                               Severity     => High_Check_Kind,
                               N            => N,
                               F1           => Var,
                               Tag          => Uninitialized,
                               Continuation => True);
            end;
         end if;

         OK := False;
      end Emit_Check_Message;

      ------------------------------
      -- Emit_Info_Message_Global --
      ------------------------------

      procedure Emit_Info_Message_Global (Var : Flow_Id) is
      begin
         --  When the Global contract is generated we don't emit any message,
         --  because it won't be obvious what such a message actually means.
         if not FA.Is_Generative then
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "initialization of & proved",
               N        => Find_Global (FA.Spec_Entity, Var),
               F1       => Var,
               Tag      => Uninitialized,
               Severity => Info_Kind);
         end if;
      end Emit_Info_Message_Global;

      -----------------------------
      -- Emit_Info_Message_Local --
      -----------------------------

      procedure Emit_Info_Message_Local (Var : Flow_Id) is
         E : constant Entity_Id := Get_Direct_Mapping_Id (Var);

      begin
         --  Skip info messages for:

         --  Variables with explicit initialization expressions, because
         --  their initialization is obvious.

         if (Ekind (E) = E_Variable
               and then (Present (Expression (Declaration_Node (E)))))

           --  Internal objects created by the frontend, because they are
           --  initialized-by-construction.

           or else
             Is_Internal (E)

           --  Auxiliary 'Result objects created by flow analysis.

           or else
             Ekind (E) = E_Function
         then
            null;
         else
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "initialization of & proved",
               N        => E,
               F1       => Var,
               Tag      => Uninitialized,
               Severity => Info_Kind);
         end if;
      end Emit_Info_Message_Local;

      ---------------------------------
      -- Has_Only_Infinite_Execution --
      ---------------------------------

      function Has_Only_Infinite_Execution (V_Final : Flow_Graphs.Vertex_Id)
                                            return Boolean
      is
         Only_Inf_Exec : Boolean := True;

         procedure Vertex_Has_Infinite_Execution
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction);

         -----------------------------------
         -- Vertex_Has_Infinite_Execution --
         -----------------------------------

         procedure Vertex_Has_Infinite_Execution
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
         begin
            if V = FA.Start_Vertex then
               --  If we reach the start vertex (remember that we are going
               --  backwards) it means that there is at least one path without
               --  an infinite loop and we can set Only_Inf_Exec to false and
               --  abort the traversal.
               Only_Inf_Exec := False;
               TV := Flow_Graphs.Abort_Traversal;

            elsif FA.Atr (V).Execution = Infinite_Loop then
               --  If we find a vertex with Infinite_Loop execution then we set
               --  Only_Inf_Exec to true and jump to another path.
               TV := Flow_Graphs.Skip_Children;

            else
               TV := Flow_Graphs.Continue;
            end if;
         end Vertex_Has_Infinite_Execution;

      --  Start of processing for Has_Only_Infinite_Execution

      begin
         FA.CFG.DFS (Start         => V_Final,
                     Include_Start => True,
                     Visitor       => Vertex_Has_Infinite_Execution'Access,
                     Reversed      => True);

         return Only_Inf_Exec;
      end Has_Only_Infinite_Execution;

      --------------
      -- Is_Array --
      --------------

      function Is_Array (F : Flow_Id) return Boolean is
        (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = Normal_Part
         and then Ekind (Get_Direct_Mapping_Id (F)) /= E_Abstract_State
         and then Is_Array_Type (Get_Type (F, FA.B_Scope)));

      ----------------------------
      -- Is_Empty_Record_Object --
      ----------------------------

      function Is_Empty_Record_Object (F : Flow_Id) return Boolean is
        (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = Normal_Part
         and then Ekind (Get_Direct_Mapping_Id (F)) /= E_Abstract_State
         and then Is_Empty_Record_Type (Get_Type (F, FA.B_Scope)));

      ----------------------
      -- Is_Init_By_Proof --
      ----------------------

      function Is_Init_By_Proof (F : Flow_Id) return Boolean is
        (F.Kind in Direct_Mapping | Record_Field
         and then Ekind (Get_Direct_Mapping_Id (F)) /= E_Abstract_State
         and then Entity_In_SPARK (Get_Direct_Mapping_Id (F))
         and then Has_Init_By_Proof (Get_Type (Entire_Variable (F),
                                               FA.B_Scope)));

      --------------------------
      -- Might_Be_Initialized --
      --------------------------

      function Might_Be_Initialized
        (Var       : Flow_Id;
         V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id)
         return Boolean
      is
         Is_Uninitialized : Boolean := False with Ghost;

      begin
         for V_Def of
           FA.DDG.Get_Collection (V_Use, Flow_Graphs.In_Neighbours)
         loop
            declare
               Def_Atr : V_Attributes renames FA.Atr (V_Def);

            begin
               if V_Def = V_Initial then
                  --  We're using the initial value
                  pragma Assert (not Def_Atr.Is_Initialized);
                  Is_Uninitialized := True;

               elsif V_Def = V_Use then
                  --  This is a self-assignment
                  null;

               elsif Def_Atr.Variables_Defined.Contains (Var)
                 or else Def_Atr.Volatiles_Read.Contains (Var)
               then
                  --  We're using a previously written value
                  if not FA.CFG.Non_Trivial_Path_Exists (V_Use, V_Def) then
                     return True;
                  end if;
               end if;
            end;
         end loop;

         pragma Assert (Is_Uninitialized);

         return False;
      end Might_Be_Initialized;

      -------------------
      -- Scan_Children --
      -------------------

      procedure Scan_Children
        (Var     : Flow_Id;
         Start   : Flow_Graphs.Vertex_Id;
         Possibly_Initialized : Boolean;
         Visited : in out Vertex_Sets.Set;
         OK      : in out Boolean)
      is
         Position : Vertex_Sets.Cursor;
         Inserted : Boolean;

      begin
         for Child of FA.PDG.Get_Collection (Start, Flow_Graphs.Out_Neighbours)
         loop
            declare
               Child_Key : Flow_Id      renames FA.DDG.Get_Key (Child);
               Child_Atr : V_Attributes renames FA.Atr (Child);

            begin
               --  Ignore final uses of non-exported objects

               if Child_Key.Variant = Final_Value
                 and then not
                   (Child_Atr.Is_Export
                      and then
                    (if Ekind (FA.Spec_Entity) = E_Package
                     then Child_Key.Kind in Direct_Mapping | Record_Field
                       and then Scope (Get_Direct_Mapping_Id (Child_Key)) =
                                  FA.Spec_Entity))
               then
                  null;
               else
                  if Is_Array (Var) then

                     Visited.Insert (New_Item => Child,
                                     Position => Position,
                                     Inserted => Inserted);

                     if not Inserted then
                        null;

                     --  Emit check if the array object is genuinely used

                     elsif Child_Atr.Variables_Explicitly_Used.Contains (Var)
                     then
                        Emit_Check_Message
                          (Var   => Var,
                           V_Use => Child,
                           Kind  =>
                             (if Possibly_Initialized
                                or else
                                 Might_Be_Initialized (Var       => Var,
                                                       V_Initial => Start,
                                                       V_Use     => Child)
                              then Unknown
                              else Err),
                           OK    => OK);

                     --  Otherwise, it is a partial assignment, e.g.
                     --     Arr (X) := Y;
                     --  which is modellled as:
                     --     Arr := (X => Y, others => Arr ("others"));
                     --  and we keep looking for genuine reads of the array.

                     else
                        Scan_Children
                          (Var,
                           Start   => Child,
                           Possibly_Initialized => True,
                           Visited => Visited,
                           OK      => OK);
                     end if;

                  else
                     if Child_Atr.Variables_Used.Contains (Var) then
                        Emit_Check_Message
                          (Var   => Var,
                           V_Use => Child,
                           Kind  =>
                             (if Might_Be_Initialized (Var       => Var,
                                                       V_Initial => Start,
                                                       V_Use     => Child)
                              then Unknown
                              else Err),
                           OK    => OK);
                     end if;
                  end if;
               end if;
            end;
         end loop;
      end Scan_Children;

      --  Local variables

      Used : Flow_Id_Sets.Set;
      --  Objects that are genuinely used by the analysed routine; only for
      --  those we want the "info: initialization proved" messages.

      Global_OK  : Flow_Id_Sets.Set;
      Global_NOK : Flow_Id_Sets.Set;
      Local_OK   : Flow_Id_Sets.Set;
      Local_NOK  : Flow_Id_Sets.Set;
      --  If all accesses to a given component happen after it is initialized,
      --  then its entire object will appear in the OK set; otherwise, its
      --  entire object will appear in the NOK set.
      --
      --  The OK/NOK containers are needed because an OK message is emitted
      --  only once for the entire object, while NOK checks are emitted for
      --  each component on each location where it accessed without being
      --  initialized.
      --
      --  The Global/Local containers are needed, because messages on global
      --  and local objects are located differently.

   --  Start of processing for Find_Use_Of_Uninitialized_Variables

   begin
      --  If this subprogram has only exceptional paths, then we already have a
      --  high check for this. We don't issue any other messages as they
      --  distract from the real issue.

      if FA.Has_Only_Exceptional_Paths then
         return;
      end if;

      for Parent of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Parent_Key : Flow_Id      renames FA.DDG.Get_Key (Parent);
            Parent_Atr : V_Attributes renames FA.Atr (Parent);

            Visited : Vertex_Sets.Set;

            OK : Boolean;
            --  This flag will be initially True, but will become False if
            --  any check is emitted when scanning the flow graph. If no such
            --  checks are emitted, then all uses of the considered object are
            --  safe and we will get a single info message.

         begin
            if Parent_Key.Variant = Initial_Value
              and then not Parent_Atr.Is_Initialized
              and then not Synthetic (Parent_Key)
              and then not Is_Empty_Record_Object (Parent_Key)
              and then not Is_Init_By_Proof (Parent_Key)
            then
               OK := True;

               Scan_Children
                 (Var     => Change_Variant (Parent_Key, Normal_Use),
                  Start   => Parent,
                  Possibly_Initialized => False,
                  Visited => Visited,
                  OK      => OK);

               --  If no checks have been emitted for any of the object
               --  components, then want an info message for the entire object.

               declare
                  Obj : constant Flow_Id :=
                    Entire_Variable
                      (Change_Variant (Parent_Key, Normal_Use));

               begin
                  if Parent_Atr.Is_Global then
                     if OK then
                        Global_OK.Include (Obj);
                     else
                        Global_NOK.Include (Obj);
                     end if;
                  else
                     if OK then
                        Local_OK.Include (Obj);
                     else
                        Local_NOK.Include (Obj);
                     end if;
                  end if;
               end;
            end if;

            --  While scanning the graph and emitting checks, we also pick
            --  objects that are actually used; this is needed for emitting
            --  messages.

            --  Ignore synthetic null output; this is an auxilary object
            if Synthetic (Parent_Key)

              --  Ignore 'Final objects that do not correspond to OUT mode
              --  parameters, Output globals, etc.

              or else (Parent_Key.Variant = Final_Value
                       and then not Parent_Atr.Is_Export)

              --  Ignore own objects of the analysed pacakge, but only for
              --  packages with a generated Initializes contract.

              or else (Parent_Key.Variant = Final_Value
                       and then Parent_Atr.Is_Export
                       and then Ekind (FA.Spec_Entity) = E_Package
                       and then No (FA.Initializes_N))

              --  Ignore implicit references to discriminants and bounds

              or else Parent_Atr.Is_Discr_Or_Bounds_Parameter

            then
               null;
            else
               for Var of Parent_Atr.Variables_Explicitly_Used loop

                  --  Ignore reads of discriminants and bounds, because they
                  --  are always initialized, even when the object is not.

                  if not Is_Discriminant (Var)
                    and then not Is_Bound (Var)
                  then
                     Used.Include (Entire_Variable (Var));
                  end if;
               end loop;
            end if;
         end;
      end loop;

      for Var of Global_OK.Difference (Global_NOK) loop
         Emit_Info_Message_Global (Var);
      end loop;

      --  We only want info messages about local objects that are actually used
      --  by the analysed subprogram.

      for Var of Local_OK.Difference (Local_NOK) loop
         if Used.Contains (Var) then
            Emit_Info_Message_Local (Var);
         end if;
      end loop;
   end Find_Use_Of_Uninitialized_Variables;

   --------------------------
   -- Find_Stable_Elements --
   --------------------------

   procedure Find_Stable_Elements (FA : in out Flow_Analysis_Graphs) is
      Done : Boolean;
      M    : Attribute_Maps.Map renames FA.Atr;
   begin
      for Loop_Id of FA.Loops loop
         Done := False;
         while not Done loop
            Done := True;
            for N_Loop of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr : V_Attributes renames M (N_Loop);

                  Is_Stable : Boolean;
               begin
                  if Atr.Loops.Contains (Loop_Id) then
                     --  For all nodes in the loop, do:

                     --  We start by checking if the used variables
                     --  contain the loop parameter for our loop.
                     if Present (Loop_Parameter_From_Loop (Loop_Id)) then
                        Is_Stable := not Atr.Variables_Used.Contains
                          (Direct_Mapping_Id
                             (Loop_Parameter_From_Loop (Loop_Id)));
                     else
                        Is_Stable := True;
                     end if;

                     --  We then check if we have at least one
                     --  in-neighbour from "outside" the loop.
                     if Is_Stable then
                        for V of FA.PDG.Get_Collection
                          (N_Loop, Flow_Graphs.In_Neighbours)
                        loop
                           if M (V).Loops.Contains (Loop_Id) then
                              Is_Stable := False;
                              exit;
                           end if;
                        end loop;
                     end if;

                     if Is_Stable then
                        --  Remove from the loop
                        Atr.Loops.Delete (Loop_Id);

                        --  Complain
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "stable",
                           N        => Error_Location (FA.PDG, FA.Atr, N_Loop),
                           Tag      => Stable,
                           Severity => Warning_Kind,
                           Vertex   => N_Loop);

                        --  There might be other stable elements now
                        Done := False;
                     end if;
                  end if;
               end;
            end loop;
         end loop;
      end loop;
   end Find_Stable_Elements;

   -----------------------------------------
   -- Find_Exports_Derived_From_Proof_Ins --
   -----------------------------------------

   procedure Find_Exports_Derived_From_Proof_Ins
     (FA : in out Flow_Analysis_Graphs)
   is
   begin
      for O in FA.Dependency_Map.Iterate loop
         declare
            Output : Flow_Id          renames Dependency_Maps.Key (O);
            Inputs : Flow_Id_Sets.Set renames FA.Dependency_Map (O);

         begin
            if Present (Output) then
               for Input of Inputs loop
                  declare
                     V : constant Flow_Graphs.Vertex_Id :=
                       Get_Initial_Vertex (FA.PDG, Input);

                  begin
                     if FA.Atr (V).Mode = Mode_Proof then
                        declare
                           use Flow_Id_Sets;

                           Path : constant Vertex_Sets.Set :=
                             Dependency_Path (FA      => FA,
                                              Input   => Input,
                                              Outputs => To_Set (Output));

                        begin
                           Error_Msg_Flow
                             (FA       => FA,
                              Path     => Path,
                              Msg      => "export & must not depend " &
                                          "on Proof_In &",
                              SRM_Ref  => "6.1.4(18)",
                              N        => Find_Global (FA.Spec_Entity,
                                                       Input),
                              F1       => Output,
                              F2       => Input,
                              Severity => Medium_Check_Kind,
                              Tag      => Export_Depends_On_Proof_In);
                        end;
                     end if;
                  end;
               end loop;
            end if;

         end;
      end loop;
   end Find_Exports_Derived_From_Proof_Ins;

   ----------------------------------------
   -- Find_Input_Only_Used_In_Assertions --
   ----------------------------------------

   procedure Find_Input_Only_Used_In_Assertions
     (FA : in out Flow_Analysis_Graphs)
   is
      use type Node_Sets.Set;

      function Only_Used_In_Assertions
        (Global_Inputs : Node_Sets.Set)
         return Node_Sets.Set
      with Post => Node_Sets.Is_Subset
                     (Subset => Only_Used_In_Assertions'Result,
                      Of_Set => Global_Inputs);
      --  Returns the subset of Global_Inputs that are only used in assertions

      function Find_In
        (User    : Node_Sets.Set;
         Objects : Flow_Id_Sets.Set)
        return Node_Sets.Set
      with Post => Node_Sets.Is_Subset (Subset => Find_In'Result,
                                        Of_Set => User);
      --  Returns the subset of User globals that are represented by Objects,
      --  either directly or by some of the encapsulating abstract states.

      -------------
      -- Find_In --
      -------------

      function Find_In
        (User    : Node_Sets.Set;
         Objects : Flow_Id_Sets.Set)
         return Node_Sets.Set
      is
         Seen : Node_Sets.Set;

      begin
         for Object of Objects loop
            if Object.Kind = Direct_Mapping then
               declare
                  Repr : constant Entity_Id :=
                    Find_In (User, Get_Direct_Mapping_Id (Object));

               begin
                  if Present (Repr) then
                     Seen.Include (Repr);
                  end if;
               end;
            end if;
         end loop;

         return Seen;
      end Find_In;

      -----------------------------
      -- Only_Used_In_Assertions --
      -----------------------------

      function Only_Used_In_Assertions (Global_Inputs : Node_Sets.Set)
                                        return Node_Sets.Set
      is
         use Flow_Graphs;

         Used_In_Assertions : Node_Sets.Set := Global_Inputs;
         Unused             : Node_Sets.Set := Global_Inputs;
         --  After traversing the graph, those will remain with Global inputs
         --  used in assertions and those not used at all, respectively.

      begin
         for V of FA.CFG.Get_Collection (All_Vertices) loop
            if Get_Key (FA.CFG, V).Variant /= Final_Value then
               declare
                  A : V_Attributes renames FA.Atr (V);

                  Used_Global_Inputs : constant Node_Sets.Set :=
                    Find_In (Global_Inputs,
                             To_Entire_Variables (A.Variables_Used));

               begin
                  if not A.Is_Assertion then
                     Used_In_Assertions.Difference (Used_Global_Inputs);
                  end if;

                  Unused.Difference (Used_Global_Inputs);
               end;
            end if;
         end loop;

         --  In Used_In_Assertions there could be some global inputs that are
         --  not used in any vertex so we need to return the difference.

         return Used_In_Assertions - Unused;
      end Only_Used_In_Assertions;

      --  Local variables

      Raw_Globals        : Raw_Global_Nodes;
      Only_Global_Inputs : Node_Sets.Set;

   --  Start of processing for Find_Input_Only_Used_In_Assertions

   begin
      if FA.Kind in Kind_Subprogram | Kind_Task
        and then Has_User_Supplied_Globals (FA.Analyzed_Entity)
      then
         Raw_Globals := Contract_Globals (FA.Spec_Entity);

         Only_Global_Inputs := Raw_Globals.Inputs - Raw_Globals.Outputs;

         for Input of Only_Used_In_Assertions (Only_Global_Inputs) loop
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& must be a Proof_In as it is only " &
                           "used in assertions",
               SRM_Ref  => "6.1.4(18)",
               N        => Find_Global (FA.Spec_Entity,
                                        Direct_Mapping_Id (Input)),
               F1       => Direct_Mapping_Id (Input),
               Tag      => Global_Wrong,
               Severity => Medium_Check_Kind);
         end loop;
      end if;
   end Find_Input_Only_Used_In_Assertions;

   ---------------------------------
   -- Find_Hidden_Unexposed_State --
   ---------------------------------

   procedure Find_Hidden_Unexposed_State (FA : in out Flow_Analysis_Graphs) is
      Pkg_Spec : constant Node_Id := Package_Specification (FA.Spec_Entity);
      Pkg_Body : constant Node_Id := Package_Body (FA.Spec_Entity);

      procedure Check_Hidden_State_Variables_And_Missing_Part_Of
        (E       : Entity_Id;
         Part_Of : Boolean)
        with Pre => Ekind (E) in E_Constant | E_Variable
                    and not Is_Internal (E)
                    and not Is_Part_Of_Concurrent_Object (E);
      --  Emits a message if:
      --  * a state variable is not mentioned as a constituent of an abstract
      --    state when it should be;
      --  * a state variable is missing the Part_Of indicator which is required
      --    by SPARK RM 7.2.6(2-3). This check is guarded by the Part_Of flag.

      procedure Traverse_Declarations (L       : List_Id;
                                       Part_Of : Boolean := False);
      --  Traverse declarations in L.
      --  Part_Of is set to True when we are in the private part of a package
      --  or in the visible part of a private child. We use this parameter to
      --  remember where we come from in the traveral and pass it to
      --  Check_Hidden_State_Variables_And_Missing_Part_Of to only emit a check
      --  about a missing Part_Of (SPARK RM 7.2.6(2-3)).

      ------------------------------------------------------
      -- Check_Hidden_State_Variables_And_Missing_Part_Of --
      ------------------------------------------------------

      procedure Check_Hidden_State_Variables_And_Missing_Part_Of
        (E       : Entity_Id;
         Part_Of : Boolean)
      is
      begin
         if Is_Constituent (E) then

            --  Detect state variable that is a Part_Of some state, but not
            --  listed in its refinement.

            declare
               State : constant Entity_Id := Encapsulating_State (E);

            begin
               if Refinement_Exists (State)
                 and then not Find_In_Refinement (State, E)
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& needs to be listed in the refinement of &",
                     N        => E,
                     F1       => Direct_Mapping_Id (E),
                     F2       => Direct_Mapping_Id (State),
                     Tag      => Hidden_Unexposed_State,
                     Severity => Medium_Check_Kind);
               end if;
            end;

         else

            --  Detect constants with variable inputs without Part_Of that do
            --  require one (SPARK RM 7.2.6(2-3)) and emit a check.

            if Part_Of
              and then Ekind (E) = E_Constant
            then
               declare
                  S : constant Node_Id := Scope (E);

                  Msg : constant String :=
                    (if Is_Child_Unit (S)
                     then "visible part of the private child"
                     else "private part of package");

                  SRM_Ref : constant String :=
                    (if Is_Child_Unit (S)
                     then "7.2.6(3)"
                     else "7.2.6(2)");

               begin
                  pragma Assert (if Is_Child_Unit (S)
                                 then Is_Private_Descendant (S)
                                 and then In_Visible_Declarations
                                            (Enclosing_Declaration (E)));

                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "indicator Part_Of is required in this "
                                 & "context: & is declared in the "
                                 & Msg & " &",
                     SRM_Ref  => SRM_Ref,
                     N        => E,
                     Severity => Error_Kind,
                     F1       => Direct_Mapping_Id (E),
                     F2       => Direct_Mapping_Id (FA.Spec_Entity));
               end;

            --  Detect hidden state and emit a message

            else
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "& needs to be a constituent " &
                              "of some state abstraction",
                  N        => E,
                  F1       => Direct_Mapping_Id (E),
                  Tag      => Hidden_Unexposed_State,
                  Severity => Medium_Check_Kind);
            end if;
         end if;
      end Check_Hidden_State_Variables_And_Missing_Part_Of;

      ---------------------------
      -- Traverse_Declarations --
      ---------------------------

      procedure Traverse_Declarations (L       : List_Id;
                                       Part_Of : Boolean := False) is
         N : Node_Id := First (L);
      begin
         while Present (N) loop
            case Nkind (N) is
               when N_Object_Declaration =>
                  declare
                     E : constant Entity_Id := Defining_Entity (N);

                  begin
                     if (Ekind (E) = E_Variable
                         or else Has_Variable_Input (E))
                       and then not Is_Internal (E)
                       and then not Is_Part_Of_Concurrent_Object (E)
                     then

                        --  Detect which of the state variables are hidden or
                        --  are missing a Part_Of indicator and emit a message.

                        Check_Hidden_State_Variables_And_Missing_Part_Of
                          (E, Part_Of);
                     end if;
                  end;

               --  N is a nested package. If the relative part is in SPARK, we
               --  recursively traverse its visible, private and body
               --  declarations.

               when N_Package_Declaration =>
                  declare
                     E        : constant Entity_Id := Defining_Entity (N);

                     Pkg_Spec : constant Node_Id := Package_Specification (E);
                     Pkg_Body : constant Node_Id := Package_Body (E);

                  begin
                     if Entity_Spec_In_SPARK (E) then

                        --  Here we traverse the visible declarations of the
                        --  nested package and we use the parameter Part_Of to
                        --  remember if we were looking for missing Part_Of
                        --  indicators.

                        Traverse_Declarations
                          (Visible_Declarations (Pkg_Spec), Part_Of);

                        --  The following is for packages that have hidden
                        --  states not exposed through an abstract state. The
                        --  case where they have abstract states will be
                        --  checked when analyzing the package itself.

                        if No (Abstract_States (E))
                          and then Private_Spec_In_SPARK (E)
                        then
                           Traverse_Declarations
                             (Private_Declarations (Pkg_Spec));

                           if Entity_Body_In_SPARK (E) then
                              Traverse_Declarations (Declarations (Pkg_Body));
                           end if;
                        end if;
                     end if;
                  end;

               when others =>
                  null;
            end case;

            Next (N);
         end loop;
      end Traverse_Declarations;

   --  Start of processing for Find_Hidden_Unexposed_State

   begin
      if Is_Child_Unit (FA.Spec_Entity)
        and then Is_Private_Descendant (FA.Spec_Entity)
      then
         --  For a private child we enforce SPARK RM 7.2.6(3) and therefore we
         --  traverse its visible declarations setting the flag Part_Of to
         --  True. Note that if the private child has or has not an abstract
         --  state does not have any influence on this because the Part_Of
         --  indicator could also denote a state abstraction declared by the
         --  parent unit of the or by a public descendant of that parent unit.

         Traverse_Declarations (Visible_Declarations (Pkg_Spec),
                                Part_Of => True);

         --  If the private child does not have an abstract state but the
         --  parent does, then we need to check if it contains any hidden state
         --  for the parent abstract state and we therefore traverse the
         --  private and body part.

         if No (Abstract_States (FA.Spec_Entity))
           and then Present (Abstract_States (Scope (FA.Spec_Entity)))
         then
            Traverse_Declarations (Private_Declarations (Pkg_Spec));

            if Entity_Body_In_SPARK (FA.Spec_Entity) then
               Traverse_Declarations (Declarations (Pkg_Body));
            end if;
         end if;

      else

         if Present (Abstract_States (FA.Spec_Entity)) then

            --  For a package with abstract states we enforce SPARK RM 7.2.6(2)
            --  and therefore we traverse its private declarations setting the
            --  flag Part_Of to True.

            Traverse_Declarations (Private_Declarations (Pkg_Spec),
                                   Part_Of => True);

            --  We also detect hidden state in the body part

            if Entity_Body_In_SPARK (FA.Spec_Entity) then
               Traverse_Declarations (Declarations (Pkg_Body));
            end if;
         end if;
      end if;
   end Find_Hidden_Unexposed_State;

   -----------------------------------------
   -- Find_Impossible_To_Initialize_State --
   -----------------------------------------

   procedure Find_Impossible_To_Initialize_State
     (FA : in out Flow_Analysis_Graphs)
   is
      DM : constant Dependency_Maps.Map :=
        Parse_Initializes (FA.Spec_Entity, FA.S_Scope);

      Outputs_Of_Procs : Flow_Id_Sets.Set;
      --  Abstracts states that are written by procedures declared in package
      --  specification.

      function Initialized_By_Initializes (F : Flow_Id) return Boolean
      with Pre => Is_Abstract_State (F);
      --  Returns True iff F is initialized by the Initializess aspect (either
      --  generated or provided by the user).

      procedure Collect_Procedure_Outputs
      with Global => (Output => Outputs_Of_Procs);
      --  Populate Outputs_Of_Procs

      function Trivially_Initialized (E : Entity_Id) return Boolean
      with Pre => Ekind (E) = E_Abstract_State;
      --  Returns True iff declaration of E says it is initialized

      --------------------------------
      -- Initialized_By_Initializes --
      --------------------------------

      function Initialized_By_Initializes (F : Flow_Id) return Boolean
        renames DM.Contains;

      -------------------------------
      -- Collect_Procedure_Outputs --
      -------------------------------

      procedure Collect_Procedure_Outputs is
         E : Entity_Id;
      begin
         E := First_Entity (FA.Spec_Entity);
         while Present (E) loop
            if Ekind (E) = E_Procedure then
               declare
                  Globals : Global_Flow_Ids;

               begin
                  Get_Globals (Subprogram => E,
                               Scope      => FA.S_Scope,
                               Classwide  => False,
                               Globals    => Globals);

                  --  If the Flow_Id is an Output (and not an Input) of the
                  --  procedure then include it in Outputs.

                  for Write of Globals.Outputs loop
                     --  ??? we should only care about abstract states of the
                     --  package that we are analyzing.
                     if Is_Abstract_State (Write)
                       and then not
                         Globals.Inputs.Contains
                           (Change_Variant (Write, In_View))
                     then
                        Outputs_Of_Procs.Include
                          (Change_Variant (Write, Normal_Use));
                     end if;
                  end loop;
               end;
            end if;

            Next_Entity (E);
         end loop;
      end Collect_Procedure_Outputs;

      function Trivially_Initialized (E : Entity_Id) return Boolean is
        (Has_Volatile (E)
         and then Has_Volatile_Property (E, Pragma_Async_Writers));

   --  Start of processing for Find_Impossible_To_Initialize_State

   begin
      if Has_Non_Null_Abstract_State (FA.Spec_Entity) then
         Collect_Procedure_Outputs;

         --  Issue error for every non-null abstract state that does not have
         --  Async_Writers, is not mentioned in an Initializes aspect and is
         --  not a pure output of an externally visible procedure.

         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            if not Trivially_Initialized (State)
                and then
              not Initialized_By_Initializes (Direct_Mapping_Id (State))
                and then
              not Outputs_Of_Procs.Contains (Direct_Mapping_Id (State))
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "no procedure exists that can initialize " &
                              "abstract state &",
                  N        => State,
                  F1       => Direct_Mapping_Id (State),
                  Tag      => Impossible_To_Initialize_State,
                  Severity => Warning_Kind);
            end if;
         end loop;
      end if;

   end Find_Impossible_To_Initialize_State;

   ----------------------------
   -- Check_Depends_Contract --
   ----------------------------

   procedure Check_Depends_Contract (FA : in out Flow_Analysis_Graphs) is

      procedure Check (Generated :     Dependency_Maps.Map;
                       User      :     Dependency_Maps.Map;
                       Missing   : out Dependency_Maps.Map;
                       Unused    : out Dependency_Maps.Map);
      --  Populate Missing and Unused with respectively missing and unused
      --  dependencies.

      function Find_Out
        (User : Dependency_Maps.Map;
         G    : Flow_Id)
         return Dependency_Maps.Cursor;
      --  Returns the clause with G or with one of its encapsulating abstract
      --  states, if they appear in the User contract; otherwise, return
      --  No_Element.

      function Strip_Proof_Ins
        (Deps : Dependency_Maps.Map)
         return Dependency_Maps.Map;
      --  Strips global Proof_Ins from the RHS of Deps

      -----------
      -- Check --
      -----------

      procedure Check (Generated :     Dependency_Maps.Map;
                       User      :     Dependency_Maps.Map;
                       Missing   : out Dependency_Maps.Map;
                       Unused    : out Dependency_Maps.Map)
      is
      begin
         Missing := Dependency_Maps.Empty_Map;
         Unused  := User;

         --  Naming convention:
         --
         --    Prefix:
         --       G = Generated,
         --       U = User-written
         --
         --    Suffix:
         --       Out = LHS,
         --       Ins = RHS,
         --       In  = RHS item

         for C in Generated.Iterate loop
            declare
               G_Out : Flow_Id          renames Dependency_Maps.Key (C);
               G_Ins : Flow_Id_Sets.Set renames Generated (C);

               U_Pos : constant Dependency_Maps.Cursor :=
                 Find_Out (User, G_Out);
               --  Position of the corresponding user-dependency clause

               U_Out : constant Flow_Id :=
                 (if Dependency_Maps.Has_Element (U_Pos)
                  then Dependency_Maps.Key (U_Pos)
                  else Null_Flow_Id);

            begin
               if Dependency_Maps.Has_Element (U_Pos) then
                  for G_In of G_Ins loop
                     declare
                        U_In : constant Flow_Id :=
                          Find_In (User (U_Pos), G_In);

                        Position : Dependency_Maps.Cursor;
                        Inserted : Boolean;

                     begin
                        if Present (U_In) then
                           Unused (U_Out).Exclude (U_In);
                           --  ??? if the RHS becomes empty where do we delete
                           --  the entire clause?

                        else
                           Missing.Insert
                             (Key      => U_Out,
                              Position => Position,
                              Inserted => Inserted);

                           Missing (Position).Insert (G_In);
                        end if;
                     end;
                  end loop;
               else
                  Missing.Insert (Key      => G_Out,
                                  New_Item => G_Ins);
               end if;
            end;
         end loop;

         --  For task T the "T => T" dependency is optional, so remove it from
         --  the Missing map (if it is there). Typically the task will always
         --  depend on itself and this dependency is optionally present in the
         --  user contract. However, a subprogram nested in the task body with
         --  the task itself among its globals, then the task might become
         --  dependent on extra items. Note: as of today, this can't really
         --  happen, because the nested subprogram body would have to either
         --  violate its own contract or be annotated with SPARK_Mode => Off.

         if Ekind (FA.Spec_Entity) = E_Task_Type then
            declare
               Task_Id : constant Flow_Id :=
                 Direct_Mapping_Id (FA.Spec_Entity);

               pragma Assert (Generated (Task_Id).Contains (Task_Id));
               --  Sanity check: "T => T" dependency is always generated

               Task_Pos : Dependency_Maps.Cursor := Missing.Find (Task_Id);

            begin
               if Dependency_Maps.Has_Element (Task_Pos) then
                  Missing (Task_Pos).Exclude (Task_Id);

                  --  If we get a "T => null" clause, then delete it

                  if Missing (Task_Pos).Is_Empty then
                     Missing.Delete (Task_Pos);
                  end if;
               end if;
            end;
         end if;
      end Check;

      --------------
      -- Find_Out --
      --------------

      function Find_Out
        (User : Dependency_Maps.Map;
         G    : Flow_Id)
         return Dependency_Maps.Cursor
      is
         C : constant Dependency_Maps.Cursor := User.Find (G);
      begin
         if Dependency_Maps.Has_Element (C) then
            return C;
         elsif Is_Constituent (G) then
            return Find_Out (User, Encapsulating_State (G));
         else
            return Dependency_Maps.No_Element;
         end if;
      end Find_Out;

      ---------------------
      -- Strip_Proof_Ins --
      ---------------------

      function Strip_Proof_Ins
        (Deps : Dependency_Maps.Map)
         return Dependency_Maps.Map
      is
         User_Globals  : Global_Flow_Ids;

         --  Global Proof_Ins cannot appear in the RHS of a Depends contract.
         --  We get them here because Compute_Dependency_Relation returns them
         --  and this is used in Find_Exports_Derived_From_Proof_Ins.

         Stripped : Dependency_Maps.Map;

      begin
         Get_Globals (FA.Analyzed_Entity, FA.B_Scope, False, User_Globals);

         for C in Deps.Iterate loop
            declare
               G_Out : Flow_Id          renames Dependency_Maps.Key (C);
               G_Ins : Flow_Id_Sets.Set renames FA.Dependency_Map (C);

               Ins : Flow_Id_Sets.Set;

            begin
               for G_In of G_Ins loop
                  if User_Globals.Proof_Ins.Contains
                      (Change_Variant (G_In, In_View))
                  then
                     null;
                  else
                     Ins.Insert (G_In);
                  end if;
               end loop;

               --  Keep the clause, except when it is "null => null"

               if Present (G_Out) or else not Ins.Is_Empty then
                  Stripped.Insert (Key      => G_Out,
                                   New_Item => Ins);
               end if;
            end;
         end loop;

         return Stripped;
      end Strip_Proof_Ins;

      --  Local variables

      User_Deps             : Dependency_Maps.Map;
      Projected_User_Deps   : Dependency_Maps.Map;
      Actual_Deps           : Dependency_Maps.Map;
      Projected_Actual_Deps : Dependency_Maps.Map;

      Missing_Deps        : Dependency_Maps.Map;
      Unused_Deps         : Dependency_Maps.Map;

      Implicit_Param : constant Entity_Id :=
        (if Is_Protected_Operation (FA.Spec_Entity)
         then Get_Implicit_Formal (FA.Analyzed_Entity)
         else Empty);
      --  Implicit formal parameter for protected operations
      --  ??? this implicit parameter is *not* an implicit dependency, so
      --  it should not be involved in any suppression, see SPARK 6.1.4:
      --
      --  "Similarly, for purposes of the rules concerning the Global,
      --  Refined_Global, Depends, and Refined_Depends aspects as they apply to
      --  protected operations, the current instance of the enclosing protected
      --  unit is considered to be a formal parameter (of mode in for a
      --  protected function, of mode in out otherwise) and a protected
      --  entry is considered to be a protected procedure."
      --
      --  And that is all what SPARK RM says abut this "implicit" parameter.

      Depends_Scope : constant Flow_Scope := (if Present (FA.Refined_Depends_N)
                                              then FA.B_Scope
                                              else FA.S_Scope);
      --  This is body scope if we are checking a Refined_Depends contract or
      --  spec scope if we are checking a Depends contract.

   --  Start of processing for Check_Depends_Contract

   begin
      --  If the user has not specified a dependency relation we have no work
      --  to do.

      if No (FA.Depends_N) then
         return;
      end if;

      --  Read the user-written Depends

      User_Deps := (if Present (FA.Refined_Depends_N)
                    then Parse_Depends (FA.Refined_Depends_N)
                    else Parse_Depends (FA.Depends_N));

      --  Read the generated Refined_Depends

      Actual_Deps := Strip_Proof_Ins (FA.Dependency_Map);

      --  Up-project the dependencies

      Up_Project (User_Deps,   Projected_User_Deps, Depends_Scope);
      Up_Project (Actual_Deps, Projected_Actual_Deps, Depends_Scope);

      --  Detect inconsistent dependencies

      Check (Generated => Projected_Actual_Deps,
             User      => Projected_User_Deps,
             Missing   => Missing_Deps,
             Unused    => Unused_Deps);

      --  Debug output

      if Debug_Trace_Depends then
         Write_Line (Get_Name_String (Chars (FA.Analyzed_Entity)) & ":");
         Print_Dependency_Map ("user",    Projected_User_Deps);
         Print_Dependency_Map ("actual",  Actual_Deps);
         Print_Dependency_Map ("missing", Missing_Deps);
         Print_Dependency_Map ("unused",  Unused_Deps);
      end if;

      for C in Unused_Deps.Iterate loop
         declare
            Unused_Out : Flow_Id renames Dependency_Maps.Key (C);
            Unused_Ins : Flow_Id_Sets.Set renames Unused_Deps (C);

         begin
            --  Detect extra LHSs in the user-written dependencies

            if Present (Unused_Out)
                and then
                not Dependency_Maps.Has_Element
                  (Find_Out (Projected_User_Deps, Unused_Out))
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "incorrect dependency & is not an output of &",
                  N        => Search_Depends_Contract
                                 (FA.Analyzed_Entity,
                                  Get_Direct_Mapping_Id (Unused_Out)),
                  F1       => Unused_Out,
                  F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag      => Depends_Null,
                  Severity => Medium_Check_Kind);
            end if;

            for Unused_In of Unused_Ins loop

               --  If the RHS mentions an extra state with visible null
               --  refinement then we suppress the check as trivially void.

               if Is_Dummy_Abstract_State (Unused_In, FA.B_Scope) then
                  null;

               --  Suppress incorrect dependencies related to implicit
               --  concurrent units, i.e. "X => CU".

               elsif Unused_Out.Kind = Direct_Mapping
                 and then Present (Implicit_Param)
                 and then Unused_In.Kind = Direct_Mapping
                 and then Implicit_Param = Get_Direct_Mapping_Id (Unused_In)
               then
                  null;

               --  Extra items on the RHS of a user dependency

               elsif not Is_Variable (Unused_In) then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& cannot appear in Depends",
                     N        => Search_Depends_Contract
                                   (FA.Analyzed_Entity,
                                    Get_Direct_Mapping_Id (Unused_Out),
                                    Get_Direct_Mapping_Id (Unused_In)),
                     F1       => Unused_In,
                     Tag      => Depends_Wrong,
                     Severity => Medium_Check_Kind);

               elsif Unused_Out = Null_Flow_Id then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "incorrect dependency ""null => %""",
                     N        => Search_Depends_Contract
                                   (FA.Analyzed_Entity,
                                    Empty,
                                    Get_Direct_Mapping_Id (Unused_In)),
                     F1       => Unused_In,
                     Tag      => Depends_Wrong,
                     Severity => Medium_Check_Kind);

               elsif Unused_Out = Direct_Mapping_Id (FA.Analyzed_Entity)
                 and then Ekind (FA.Analyzed_Entity) = E_Function
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "incorrect dependency ""%'Result => %""",
                     N        => Search_Depends_Contract
                                   (FA.Analyzed_Entity,
                                    Get_Direct_Mapping_Id (Unused_Out),
                                    Get_Direct_Mapping_Id (Unused_In)),
                     F1       => Unused_Out,
                     F2       => Unused_In,
                     Tag      => Depends_Wrong,
                     Severity => Medium_Check_Kind);

               else
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "incorrect dependency ""% => %""",
                     N        => Search_Depends_Contract
                                   (FA.Analyzed_Entity,
                                    Get_Direct_Mapping_Id (Unused_Out),
                                    Get_Direct_Mapping_Id (Unused_In)),
                     F1       => Unused_Out,
                     F2       => Unused_In,
                     Tag      => Depends_Wrong,
                     Severity => Medium_Check_Kind);
               end if;
            end loop;
         end;
      end loop;

      for C in Missing_Deps.Iterate loop
         declare
            Missing_Out : Flow_Id renames Dependency_Maps.Key (C);
            Missing_Ins : Flow_Id_Sets.Set renames Missing_Deps (C);

         begin
            if not Dependency_Maps.Has_Element
              (Find_Out (User_Deps, Missing_Out))
            then
               if Present (Implicit_Param)
                 and then Missing_Out = Direct_Mapping_Id (Implicit_Param)
               then
                  null;

               elsif Missing_Out = Null_Flow_Id then
                  null;

               else
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "expected to see & on the left-hand-side of" &
                                 " a dependency relation",
                     N        => FA.Depends_N,
                     F1       => Missing_Out,
                     Tag      => Depends_Missing_Clause,
                     Severity => Medium_Check_Kind);
               end if;
            end if;

            for Missing_In of Missing_Ins loop
               if Missing_Out = Null_Flow_Id
                 and then Missing_In.Kind = Direct_Mapping
                 and then Present (Implicit_Param)
                 and then Implicit_Param = Get_Direct_Mapping_Id (Missing_In)
               then
                  null;

               --  Items missing from the RHS of a user dependency

               else
                  if Missing_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "missing dependency ""null => %""",
                        N        => FA.Depends_N,
                        F1       => Missing_In,
                        Tag      => Depends_Null,
                        Severity => Medium_Check_Kind);
                  else
                     declare
                        use Flow_Id_Sets;

                        Path : constant Vertex_Sets.Set :=
                          Dependency_Path (FA      => FA,
                                           Input   => Missing_In,
                                           Outputs => To_Set (Missing_Out));

                     begin
                        if Missing_Out = Direct_Mapping_Id (FA.Analyzed_Entity)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Path     => Path,
                              Msg      => "missing dependency ""%'Result => " &
                                          "%""",
                              N        => Search_Depends_Contract
                                             (FA.Analyzed_Entity,
                                              FA.Analyzed_Entity),
                              F1       => Missing_Out,
                              F2       => Missing_In,
                              Tag      => Depends_Missing,
                              Severity => Medium_Check_Kind);

                        else
                           declare
                              N : constant Node_Id :=
                                Search_Depends_Contract
                                  (FA.Analyzed_Entity,
                                   Get_Direct_Mapping_Id (Missing_Out));

                              Kind : constant String :=
                                (if Missing_Out = Missing_In
                                 then "self-dependency "
                                 else "dependency ");

                              Hint : constant String :=
                                (if Missing_Out = Missing_In then
                                   (if Has_Bounds (Missing_Out, FA.B_Scope)
                                    then " (array bounds are preserved)"
                                    elsif Contains_Discriminants (Missing_Out,
                                                                  FA.B_Scope)
                                    then " (discriminants are preserved)"
                                    else "")
                                 else "");

                           begin
                              Error_Msg_Flow
                                (FA       => FA,
                                 Path     => Path,
                                 Msg      => "missing " & Kind & """% => %""" &
                                             Hint,
                                 N        => N,
                                 F1       => Missing_Out,
                                 F2       => Missing_In,
                                 Tag      => Depends_Missing,
                                 Severity => Medium_Check_Kind);
                           end;
                        end if;
                     end;
                  end if;
               end if;
            end loop;
         end;
      end loop;
   end Check_Depends_Contract;

   -----------------------------------
   -- Check_Ghost_Procedure_Outputs --
   -----------------------------------

   procedure Check_Ghost_Procedure_Outputs (FA : in out Flow_Analysis_Graphs)
   is
      Globals : Global_Flow_Ids;
   begin
      if Ekind (FA.Analyzed_Entity) = E_Procedure
        and then Is_Ghost_Entity (FA.Analyzed_Entity)
      then
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         for Output of Globals.Outputs loop
            if not Is_Ghost_Entity (Output) then
               Error_Msg_Flow (FA       => FA,
                               Msg      => "ghost procedure & cannot have " &
                                           "non-ghost global output &",
                               N        => FA.Analyzed_Entity,
                               F1       => Direct_Mapping_Id
                                             (FA.Analyzed_Entity),
                               F2       => Output,
                               Severity => Medium_Check_Kind,
                               Tag      => Ghost_Wrong,
                               SRM_Ref  => "6.9(20)");
            end if;
         end loop;
      end if;
   end Check_Ghost_Procedure_Outputs;

   -------------------------------------------
   -- Check_Consistent_AS_For_Private_Child --
   -------------------------------------------

   procedure Check_Consistent_AS_For_Private_Child
     (FA : in out Flow_Analysis_Graphs)
   is
   begin
      if Is_Child_Unit (FA.Spec_Entity)
        and then Is_Private_Descendant (FA.Spec_Entity)
      then
         for Child_State of Iter (Abstract_States (FA.Spec_Entity)) loop
            declare
               Encapsulating : constant Entity_Id :=
                 Encapsulating_State (Child_State);

            begin
               if Present (Encapsulating) then
                  if Refinement_Exists (Encapsulating)
                    and then not Find_In_Refinement (Encapsulating,
                                                     Child_State)
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "refinement of % shall mention %",
                        Severity => Error_Kind,
                        F1       => Direct_Mapping_Id (Encapsulating),
                        F2       => Direct_Mapping_Id (Child_State),
                        N        => Scope (Encapsulating),
                        SRM_Ref  => "7.2.6(6)");
                  end if;
               end if;
            end;
         end loop;
      end if;
   end Check_Consistent_AS_For_Private_Child;

   --------------------------------
   -- Check_Initializes_Contract --
   --------------------------------

   procedure Check_Initializes_Contract (FA : in out Flow_Analysis_Graphs) is
      DM : constant Dependency_Maps.Map :=
        Parse_Initializes (FA.Spec_Entity, FA.S_Scope);

      function Is_Written (Comp : Flow_Id) return Boolean;
      --  Returns True iff Comp is definitely written, according to the PDG

      function Find_RHS (LHS : Flow_Id) return Flow_Id_Sets.Set;
      --  Returns what the LHS depends on

      ----------------
      -- Is_Written --
      ----------------

      function Is_Written (Comp : Flow_Id) return Boolean is
      begin
         --  If we get an abstract state here, we are either in a nested
         --  package or in a private child without a body yet. We consider the
         --  abstract state to be written only if it is mentioned in the
         --  (generated) Initializes contract of the enclosing package.
         --
         --  ??? We shouldn't need this code and the initialization status for
         --  such abstract state should be directly looked in the PDG. This
         --  means that we should set the Is_Export flag for those abstract
         --  states that are initialized.

         if Is_Abstract_State (Comp) then
            declare
               AS : constant Entity_Id := Get_Direct_Mapping_Id (Comp);
               Enclosing_Pkg : constant Entity_Id := Scope (AS);

            begin
               return Enclosing_Pkg /= FA.Spec_Entity
                 and then
               Parse_Initializes (Enclosing_Pkg, FA.B_Scope).Contains (Comp);
            end;
         end if;

         declare
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
               return not FA.PDG.Edge_Exists (Comp_Initial, Comp_Final);
            end if;
         end;
      end Is_Written;

      --------------
      -- Find_RHS --
      --------------

      function Find_RHS (LHS : Flow_Id) return Flow_Id_Sets.Set is
         LHS_Final : constant Flow_Graphs.Vertex_Id :=
           FA.PDG.Get_Vertex (Change_Variant (LHS, Final_Value));
      begin
         return Dependency (FA, LHS_Final);
      end Find_RHS;

   --  Start of processing for Check_Initializes_Contract

   begin
      --  For library-level packages check if everything in the RHS of an
      --  initialization_item is indeed initialized.

      if Is_Library_Level_Entity (FA.Analyzed_Entity) then
         declare
            Found_Uninitialized : Boolean := False;

         begin
            for C in DM.Iterate loop
               declare
                  The_Out : Flow_Id          renames Dependency_Maps.Key (C);
                  The_Ins : Flow_Id_Sets.Set renames DM (C);

               begin
                  for G of The_Ins loop
                     if not Is_Initialized_At_Elaboration (G, FA.B_Scope) then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "% must be initialized at elaboration",
                           N        => (if Present (FA.Initializes_N)
                                        then Search_Initializes_Contract
                                          (FA.Spec_Entity,
                                           Get_Direct_Mapping_Id (The_Out),
                                           Get_Direct_Mapping_Id (G))
                                        else FA.Spec_Entity),
                           F1       => G,
                           Severity => High_Check_Kind,
                           Tag      => Uninitialized);
                        Found_Uninitialized := True;
                     end if;
                  end loop;
               end;
            end loop;

            --  If a variable or state abstraction that has not been mentioned
            --  in an Initializes aspect was found in the RHS of an
            --  initialization_item then we don't do any further analysis.

            if Found_Uninitialized then
               return;
            end if;
         end;
      end if;

      --  If we are dealing with a generated initializes aspect then we have no
      --  more checks to do.

      if No (FA.Initializes_N) then
         return;
      end if;

      for C in DM.Iterate loop
         declare
            The_Out : Flow_Id          renames Dependency_Maps.Key (C);
            The_Ins : Flow_Id_Sets.Set renames DM (C);

            All_Contract_Outs : constant Flow_Id_Sets.Set :=
              Down_Project (The_Out, FA.B_Scope);

            All_Contract_Ins  : constant Flow_Id_Sets.Set :=
              Down_Project (The_Ins, FA.B_Scope);

            All_Actual_Ins    : Flow_Id_Sets.Set;

         begin
            for Contract_Out of All_Contract_Outs loop

               --  The down-projectd LHS contains only constants, variables and
               --  abstract states of nested packages, all known by Entity_Id.

               pragma Assert
                 (Contract_Out.Kind = Direct_Mapping
                  and then Ekind (Get_Direct_Mapping_Id (Contract_Out)) in
                    E_Abstract_State | E_Constant | E_Variable);

               --  If the currently analyzed user LHS is variable, then collect
               --  its actual dependencies; otherwise, reject it as a constant
               --  without variable input.

               if Is_Variable (Contract_Out) then
                  declare
                     Actual_Out : constant Dependency_Maps.Cursor :=
                       FA.Dependency_Map.Find (Contract_Out);

                  begin
                     if Dependency_Maps.Has_Element (Actual_Out) then
                        All_Actual_Ins.Union (FA.Dependency_Map (Actual_Out));
                     end if;
                  end;

               --  Emit message only for constants without variable input
               --  declared in the visible part of the analyzed package; here
               --  we might get other constants that are constituents of an
               --  abstract state of the analyzed package, but we will flag
               --  them when checking the Refined_State/Part_Of contracts.

               else
                  declare
                     E : constant Entity_Id :=
                       Get_Direct_Mapping_Id (Contract_Out);

                  begin
                     if Get_Flow_Scope (E) = (FA.Spec_Entity, Visible_Part)
                     then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& cannot appear in Initializes",
                           N        => Search_Initializes_Contract
                                         (FA.Spec_Entity,
                                          E),
                           F1       => Contract_Out,
                           Tag      => Initializes_Wrong,
                           Severity => Medium_Check_Kind);
                     end if;
                  end;
               end if;
            end loop;

            --  Detect inputs missing from the RHS

            for Actual_In of All_Actual_Ins loop
               if not All_Contract_Ins.Contains (Actual_In) then
                  declare
                     Path : constant Vertex_Sets.Set :=
                       Dependency_Path (FA      => FA,
                                        Input   => Actual_In,
                                        Outputs => All_Contract_Outs);

                  begin
                     Error_Msg_Flow
                       (FA       => FA,
                        Path     => Path,
                        Msg      => "initialization of % must not depend on %",
                        SRM_Ref  => "7.1.5(11)",
                        N        => Search_Initializes_Contract
                                      (FA.Spec_Entity,
                                       Get_Direct_Mapping_Id (The_Out)),
                        F1       => The_Out,
                        F2       => Actual_In,
                        Tag      => Initializes_Wrong,
                        Severity => Medium_Check_Kind);
                  end;
               end if;
            end loop;

            --  Detect extra inputs on the RHS

            for Contract_In of All_Contract_Ins loop
               if not All_Actual_Ins.Contains (Contract_In) then
                  if Is_Variable (Contract_In) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "initialization of & does not depend on &",
                        SRM_Ref  => "7.1.5(11)",
                        N        => Search_Initializes_Contract
                                      (FA.Spec_Entity,
                                       Get_Direct_Mapping_Id (The_Out),
                                       Get_Direct_Mapping_Id (Contract_In)),
                        F1       => The_Out,
                        F2       => Contract_In,
                        Tag      => Initializes_Wrong,
                        Severity => Medium_Check_Kind);

                  else

                     --  The input is a constant without variable input

                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& cannot appear in Initializes",
                        N        => Search_Initializes_Contract
                                      (FA.Spec_Entity,
                                       Get_Direct_Mapping_Id (The_Out),
                                       Get_Direct_Mapping_Id (Contract_In)),
                        F1       => Contract_In,
                        Tag      => Initializes_Wrong,
                        Severity => Medium_Check_Kind);
                  end if;
               end if;
            end loop;
         end;
      end loop;

      --  Detect objects missing from the LHS of the Initializes

      --  ??? Maybe we could avoid calling GG_Get_Local_Variables and retrieve
      --  this information from the AST.

      for Var of GG_Get_Local_Variables (FA.Spec_Entity) loop
         declare
            LHS            : constant Flow_Id := Direct_Mapping_Id (Var);
            RHS            : Flow_Id_Sets.Set;
            LHS_Components : Flow_Id_Sets.Set;

         begin
            if not DM.Contains (LHS) then
               for Constituent of Down_Project (Var, FA.B_Scope) loop

                  --  ??? It would be better if we wouldn't get things that are
                  --  not in SPARK here but at the moment Down_Project does
                  --  returns them. This need to be fixed in Down_Project.

                  if Is_Abstract_State (Constituent)
                    or else Entity_In_SPARK (Constituent)
                  then
                     for C of Flatten_Variable (Constituent, FA.B_Scope) loop
                        LHS_Components.Insert (C);
                     end loop;
                  end if;

               end loop;

               if (for all Comp of LHS_Components => Is_Written (Comp)) then

                  --  Check if the LHS depends on some inputs that will have to
                  --  be mentioned in the RHS of the clause.

                  for LHS of LHS_Components loop
                     RHS.Union (Find_RHS (LHS));
                  end loop;

                  --  LHS does not depend on any input

                  if RHS.Is_Empty then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "initialization of & must be mentioned " &
                                    "in the Initializes contract of &",
                        N        => Var,
                        F1       => LHS,
                        F2       => Direct_Mapping_Id (FA.Spec_Entity),
                        SRM_Ref  => "7.1.5(9)",
                        Tag      => Initializes_Wrong,
                        Severity => Low_Check_Kind);

                  --  LHS does depends on some inputs and we need to list them
                  --  in the contract.

                  else
                     for Input of RHS loop
                        declare
                           use Flow_Id_Sets;

                           Outputs : constant Flow_Id_Sets.Set := To_Set (LHS);

                           Path : constant Vertex_Sets.Set :=
                             Dependency_Path
                               (FA      => FA,
                                Input   => Change_Variant (Input, Normal_Use),
                                Outputs => Outputs);

                        begin
                           Error_Msg_Flow
                             (FA       => FA,
                              Path     => Path,
                              Msg      => "initialization of & through & " &
                                          "must be listed in the " &
                                          "Initializes contract",
                              N        => Var,
                              F1       => LHS,
                              F2       => Input,
                              SRM_Ref  => "7.1.5(9)",
                              Tag      => Initializes_Wrong,
                              Severity => Low_Check_Kind);
                        end;
                     end loop;
                  end if;
               end if;
            end if;
         end;
      end loop;
   end Check_Initializes_Contract;

   ----------------------------------
   -- Check_Refined_State_Contract --
   ----------------------------------

   procedure Check_Refined_State_Contract (FA : in out Flow_Analysis_Graphs) is

      procedure Error_Msg (N : Node_Id; E : Entity_Id; Msg : String);
      --  Emit message Msg about constant without variable input E; the message
      --  will be attached to N.

      ---------------
      -- Error_Msg --
      ---------------

      procedure Error_Msg (N : Node_Id; E : Entity_Id; Msg : String) is
      begin
         Error_Msg_Flow
           (FA       => FA,
            Msg      => Msg,
            N        => N,
            F1       => Direct_Mapping_Id (E),
            SRM_Ref  => "7.2.2(16)",
            Tag      => Refined_State_Wrong,
            Severity => Medium_Check_Kind);
      end Error_Msg;

   --  Start of processing for Check_Refined_State_Contract

   begin
      if Has_Non_Null_Abstract_State (FA.Spec_Entity) then

         --  If package body is in SPARK, then look at the Refined_State
         --  contract (ignoring abstract states with null refinement).

         if Entity_Body_In_SPARK (FA.Spec_Entity) then
            declare
               Refined_State_N : constant Node_Id :=
                 Get_Pragma (FA.Analyzed_Entity, Pragma_Refined_State);

            begin
               for State of Iter (Abstract_States (FA.Spec_Entity)) loop
                  if not Has_Null_Refinement (State) then
                     for Constituent of Iter (Refinement_Constituents (State))
                     loop
                        if Ekind (Constituent) = E_Constant
                          and then not Has_Variable_Input (Constituent)
                        then
                           Error_Msg (Refined_State_N,
                                      Constituent,
                                      "& cannot appear in Refined_State");
                        end if;
                     end loop;
                  end if;
               end loop;
            end;

         --  If only package spec is in SPARK, then look at Part_Of
         --  constituents.

         elsif Entity_Spec_In_SPARK (FA.Spec_Entity) then

            for State of Iter (Abstract_States (FA.Spec_Entity)) loop
               for Constituent of Iter (Part_Of_Constituents (State)) loop

                  --  Part_Of indicator can be applied to entities in packages
                  --  nested in the private part of the currently analyzed one
                  --  and those packages can have SPARK_Mode => Off. We detect
                  --  this by checking whether the constituent is in SPARK.

                  if Ekind (Constituent) = E_Constant
                    and then Entity_In_SPARK (Constituent)
                    and then not Has_Variable_Input (Constituent)
                  then
                     Error_Msg (Declaration_Node (Constituent),
                                Constituent,
                                "& cannot have a Part_Of indicator");
                  end if;
               end loop;
            end loop;

         end if;
      end if;

   end Check_Refined_State_Contract;

   --------------------------------
   -- Check_Potentially_Blocking --
   --------------------------------

   procedure Check_Potentially_Blocking (FA : in out Flow_Analysis_Graphs) is

      function Is_Delay_Statement (F : Flow_Id) return Boolean;
      --  Return True iff F represent a delay statement

      ------------------------
      -- Is_Delay_Statement --
      ------------------------

      function Is_Delay_Statement (F : Flow_Id) return Boolean is
      begin
         --  Match attributes of vertices created in Do_Delay_Statement
         return
           F.Kind = Direct_Mapping
             and then Nkind (Get_Direct_Mapping_Id (F)) in N_Delay_Statement;
      end Is_Delay_Statement;

      --  Local variables

      Context : constant Entity_Id := Scope (FA.Spec_Entity);

   --  Start of processing for Check_Potentially_Blocking

   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

            Blocking_Callee       : Any_Entity_Name;
            Call_With_Same_Target : External_Call;
            --  Will keep a detailed reason for operations that are potentially
            --  blocking due to indirect calls to other subprograms.

         begin
            if Atr.Is_Program_Node
              and then Is_Delay_Statement (FA.CFG.Get_Key (V))
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "potentially blocking delay statement " &
                    "in protected operation &",
                  N        => Atr.Error_Location,
                  F1       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag      => Potentially_Blocking_In_Protected,
                  Severity => High_Check_Kind);
            else
               for E of Atr.Subprograms_Called loop

                  --  Calls to entries are trivially potentially blocking

                  if Is_Entry (E) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "potentially blocking entry call " &
                          "in protected operation &",
                        N        => Atr.Error_Location,
                        F1       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Potentially_Blocking_In_Protected,
                        Severity => High_Check_Kind);

                  --  Predefined potentially blocking routines are identified
                  --  individually, because they are not analyzed in phase 1.

                  elsif In_Predefined_Unit (E) then
                     if Is_Predefined_Potentially_Blocking (E) then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             "call to potentially blocking " &
                             "predefined subprogram & " &
                             "in protected operation &",
                           N        => Atr.Error_Location,
                           F1       => Direct_Mapping_Id (E),
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag      => Potentially_Blocking_In_Protected,
                           Severity => High_Check_Kind);
                     end if;

                  --  Direct calls to potentially blocking subprograms

                  elsif Has_Potentially_Blocking_Statement (E) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "call to potentially blocking subprogram & " &
                          "in protected operation &",
                        N        => Atr.Error_Location,
                        F1       => Direct_Mapping_Id (E),
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Potentially_Blocking_In_Protected,
                        Severity => High_Check_Kind);

                  --  ??? For indirect calls we would prefer to emit a detailed
                  --  trace of calls that leads to a potentially blocking
                  --  operation, but this requires storing the slocs of both
                  --  direct calls and potentially blocking operations within
                  --  the ALI file and a copy of the original call graph (and
                  --  not its transitive closure).

                  else

                     --  Indirect calls to potentially blocking subprograms

                     Blocking_Callee := Potentially_Blocking_Callee (E);

                     if Blocking_Callee /= Null_Entity_Name then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             "call to potentially blocking subprogram & " &
                             "in protected operation &",
                           N        => Atr.Error_Location,
                           F1       => Magic_String_Id (Blocking_Callee),
                           F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag      => Potentially_Blocking_In_Protected,
                           Severity => High_Check_Kind);

                     --  An external call on a protected subprogram with the
                     --  same target object as that of the protected action.

                     else
                        Call_With_Same_Target :=
                          Potentially_Blocking_External_Call (E, Context);

                        if Present (Call_With_Same_Target.Protected_Subprogram)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "external call to & from & " &
                                "in protected operation &",
                              N        => Atr.Error_Location,
                              F1       =>
                                Direct_Mapping_Id
                                  (Call_With_Same_Target.Protected_Subprogram),

                              F2       =>
                                Magic_String_Id
                                  (Call_With_Same_Target. External_Callee),

                              F3       =>
                                Direct_Mapping_Id (FA.Analyzed_Entity),

                              Tag      => Potentially_Blocking_In_Protected,
                              Severity => High_Check_Kind);
                        end if;
                     end if;
                  end if;
               end loop;
            end if;
         end;
      end loop;
   end Check_Potentially_Blocking;

   -------------------------------------
   -- Check_Prefixes_Of_Attribute_Old --
   -------------------------------------

   procedure Check_Prefixes_Of_Attribute_Old
     (FA : in out Flow_Analysis_Graphs)
   is

      function Check_Prefix (N : Node_Id) return Traverse_Result;
      --  If N is a 'Old attribute then issue a high check for every
      --  variable that is part of the prefix of the 'Old and is not
      --  an import.

      ------------------
      -- Check_Prefix --
      ------------------

      function Check_Prefix (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Get_Attribute_Id (Attribute_Name (N)) = Attribute_Old
         then
            declare
               Vars : constant Flow_Id_Sets.Set :=
                 Get_Variables
                   (N,
                    Scope                => FA.B_Scope,
                    Fold_Functions       => False,
                    Use_Computed_Globals => True);

            begin

               for Var of Vars loop
                  declare
                     Initial_V : constant Flow_Graphs.Vertex_Id :=
                       Get_Initial_Vertex (FA.CFG, Var);

                  begin
                     if not FA.Atr (Initial_V).Is_Import then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& is not initialized " &
                                       "at subprogram entry",
                           Severity => High_Check_Kind,
                           N        => First_Variable_Use
                                         (N       => N,
                                          Scope   => FA.B_Scope,
                                          Var     => Var,
                                          Precise => False),
                           F1       => Var,
                           Tag      => Uninitialized);
                     end if;
                  end;
               end loop;
            end;
         end if;

         return OK;
      end Check_Prefix;

      procedure Check_Prefix_Of_Tick_Old is new
        Traverse_More_Proc (Process => Check_Prefix);

      Postconditions : Node_Lists.List;

   begin
      for Refined in Boolean loop
         Postconditions := Get_Postcondition_Expressions
           (FA.Analyzed_Entity,
            Refined);

         for Postcondition of Postconditions loop
            Check_Prefix_Of_Tick_Old (Postcondition);
         end loop;
      end loop;
   end Check_Prefixes_Of_Attribute_Old;

   --------------------
   -- Check_Aliasing --
   --------------------

   procedure Check_Aliasing (FA : in out Flow_Analysis_Graphs) is

      function Is_Inlined_Subprogram_Call (F : Flow_Id) return Boolean;
      --  Return True iff F represents a subprogram call that was inlined for
      --  proof.

      --------------------------------
      -- Is_Inlined_Subprogram_Call --
      --------------------------------

      function Is_Inlined_Subprogram_Call (F : Flow_Id) return Boolean is
      begin
         if F.Kind = Direct_Mapping then
            declare
               N : constant Node_Id := Get_Direct_Mapping_Id (F);
            begin
               --  Subprogram calls that were inlined by the frontend are
               --  represented as null statements with the original call
               --  statement kept in the Original_Node.

               return Nkind (N) = N_Null_Statement
                 and then Nkind (Original_Node (N)) in N_Subprogram_Call;
            end;
         else
            return False;
         end if;
      end Is_Inlined_Subprogram_Call;

   --  Start of processing for Check_Aliasing

   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
            Key : Flow_Id      renames FA.CFG.Get_Key (V);

         begin
            if Atr.Is_Callsite then
               Antialiasing.Check_Procedure_Call
                 (FA => FA,
                  N  => Get_Direct_Mapping_Id (Key));
            elsif Is_Inlined_Subprogram_Call (Key) then
               Antialiasing.Check_Procedure_Call
                 (FA => FA,
                  N  => Original_Node (Get_Direct_Mapping_Id (Key)));
            end if;
         end;
      end loop;
   end Check_Aliasing;

   --------------------------------------
   -- Check_Constant_After_Elaboration --
   --------------------------------------

   procedure Check_Constant_After_Elaboration
     (FA : in out Flow_Analysis_Graphs)
   is
      Package_Elaboration : constant Boolean :=
        Ekind (FA.Spec_Entity) = E_Package;

      procedure Check_Subprogram (E : Entity_Id);
      --  Inspects globals of subprogram E to detect violations of SPARK RM
      --  6.1.4(21).

      ----------------------
      -- Check_Subprogram --
      ----------------------

      procedure Check_Subprogram (E : Entity_Id) is
         procedure Emit_Check (Globals : Flow_Id_Sets.Set);
         --  Emit check when SRM 6.1.4(21) is violated

         ----------------
         -- Emit_Check --
         ----------------

         procedure Emit_Check (Globals : Flow_Id_Sets.Set) is
         begin
            for Global of Globals loop
               if Is_Constant_After_Elaboration (Global) then
                  if Package_Elaboration then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "subprogram & with global constant " &
                                    "after elaboration & must not be called " &
                                    "during elaboration of &",
                        Severity => High_Check_Kind,
                        N        => FA.Analyzed_Entity,
                        --  ??? This error location should be improved
                        F1       => Direct_Mapping_Id (E),
                        F2       => Global,
                        F3       => Direct_Mapping_Id (FA.Spec_Entity),
                        SRM_Ref  => "6.1.4(21)",
                        Tag      => Not_Constant_After_Elaboration);

                  else
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "constant after elaboration & must not " &
                                    "be an output of subprogram &",
                        Severity => High_Check_Kind,
                        N        => FA.Analyzed_Entity,
                        --  ??? This error location should be improved
                        F1       => Global,
                        F2       => Direct_Mapping_Id (FA.Spec_Entity),
                        SRM_Ref  => "6.1.4(21)",
                        Tag      => Not_Constant_After_Elaboration);
                  end if;
               end if;
            end loop;
         end Emit_Check;

         Globals : Global_Flow_Ids;

      --  Start of processing for Check_Subprogram

      begin
         Get_Globals (Subprogram => E,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         --  Check that the elaboration of a library-level package does not
         --  call a subprogram or entry having an Input or Proof_In global
         --  marked as constant after elaboration.

         if Package_Elaboration then

            Emit_Check (Globals.Inputs);
            Emit_Check (Globals.Proof_Ins);

         --  Check that the procedure/entry/task does not modify variables
         --  that have Constant_After_Elaboration set.

         else

            Emit_Check (Globals.Outputs);

         end if;
      end Check_Subprogram;

   --  Start of processing for Check_Constant_After_Elaboration

   begin
      case Ekind (FA.Spec_Entity) is

         --  Check calls of a package elaboration

         when E_Package =>
            if Is_Library_Level_Entity (FA.Spec_Entity) then
               for Call of Generated_Calls (FA.Spec_Entity) loop
                  if Is_Subprogram (Call)
                    or else Is_Entry (Call)
                  then
                     Check_Subprogram (Call);
                  end if;
               end loop;
            end if;

         --  Check procedures/entries/tasks

         when E_Procedure
            | E_Entry
            | E_Task_Type
         =>
            Check_Subprogram (FA.Spec_Entity);

         when E_Function =>
            null;

         when others =>
            raise Program_Error;

      end case;
   end Check_Constant_After_Elaboration;

   -----------------------------------------
   -- Check_Function_For_Volatile_Effects --
   -----------------------------------------

   procedure Check_Function_For_Volatile_Effects
     (FA : in out Flow_Analysis_Graphs)
   is
      Volatile_Effect_Found    : Boolean := False;
      Volatile_Effect_Expected : Boolean;

      procedure Check_Set_For_Volatiles (FS : Flow_Id_Sets.Set);
      --  Emits a high check for every volatile variable found in FS.
      --  @param FS is the Flow_Ids set that will be checked for volatiles

      -----------------------------
      -- Check_Set_For_Volatiles --
      -----------------------------

      procedure Check_Set_For_Volatiles (FS : Flow_Id_Sets.Set) is
      begin
         for F of FS loop
            if Is_Volatile (F) then

               --  We just found a volatile effect

               Volatile_Effect_Found := True;

               --  Issue error if dealing with nonvolatile function; SPARK RM
               --  7.1.3(8).

               if not Volatile_Effect_Expected then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& cannot act as global item of " &
                                 "nonvolatile function &",
                     Severity => Error_Kind,
                     N        => FA.Analyzed_Entity,
                     F1       => F,
                     F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag      => Non_Volatile_Function_With_Volatile_Effects);
               end if;
            end if;
         end loop;
      end Check_Set_For_Volatiles;

   --  Start of processing for Check_Function_For_Volatile_Effects

   begin
      if Ekind (FA.Analyzed_Entity) /= E_Function then

         --  If we are not dealing with a function then we have nothing to do
         --  here.

         return;
      end if;

      Volatile_Effect_Expected :=
        (if Is_Protected_Type (Scope (FA.Analyzed_Entity))
         then Is_Volatile_For_Internal_Calls (FA.Analyzed_Entity)
         else Is_Volatile_Function (FA.Analyzed_Entity));

      declare
         Globals : Global_Flow_Ids;

      begin
         --  Populate global sets using (possibly generated) Global from the
         --  function specification.

         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.S_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         --  Check globals for volatiles and emit messages if needed. Sets
         --  Proof_Ins and Reads are disjoint, so it is more efficient to
         --  process them separately instead of computing union; Writes of a
         --  function, after sanity checks, are known to be empty.

         Check_Set_For_Volatiles (Globals.Proof_Ins);
         Check_Set_For_Volatiles (Globals.Inputs);
         pragma Assert (Globals.Outputs.Is_Empty);
      end;

      --  The function is volatile if its parameters are of a volatile type

      Volatile_Effect_Found :=
        Volatile_Effect_Found
        or else (for some F of Get_Explicit_Formals (FA.Analyzed_Entity)
                 => Is_Effectively_Volatile (Etype (F)));

      --  Warn about volatile function without volatile effects

      if Volatile_Effect_Expected
        and then not Volatile_Effect_Found
      then
         Error_Msg_Flow
           (FA       => FA,
            Msg      => "volatile function & has no volatile effects",
            Severity => Warning_Kind,
            N        => FA.Analyzed_Entity,
            F1       => Direct_Mapping_Id (FA.Analyzed_Entity),
            Tag      => Volatile_Function_Without_Volatile_Effects);
      end if;
   end Check_Function_For_Volatile_Effects;

   -------------------------------
   -- Check_Concurrent_Accesses --
   -------------------------------

   procedure Check_Concurrent_Accesses (GNAT_Root : Node_Id) is
      subtype Simple_Owning_Kind is Tasking_Owning_Kind
        with Static_Predicate =>
          Simple_Owning_Kind in Suspends_On | Unsynch_Accesses;
      --  Checks for suspending on suspension objects and accessing
      --  unsynchronized variables is similar and simple; this type helps to
      --  reuse it.

      package Name_To_Name_Lists is new
        Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                    Element_Type    => Name_Lists.List,
                                    Hash            => Name_Hash,
                                    Equivalent_Keys => "=",
                                    "="             => Name_Lists."=");
      --  Maps from objects to lists of task types that access them

      Object_Owners : array (Tasking_Owning_Kind) of Name_To_Name_Lists.Map;
      --  Mapping from objects to lists of task types that owns them, i.e.
      --  suspend on a suspension object, access an unsynchronized variable or
      --  call a protected entry.

      function Msg_Attach_Node
        (Task_Name   : Entity_Name;
         Object_Name : Entity_Name)
         return Entity_Id;
      --  Returns an entity for attaching the error message. It is preferably
      --  the entity designated by Task_Name. However, if it is declared in a
      --  body of a with-ed package then we have no Entity_Id for that; then we
      --  try with the Object_Name; then the best we can get is the root entity
      --  of the current compilation unit.

      procedure Check_Ownership (Owning_Kind : Simple_Owning_Kind);
      --  Check ownership of a kind Owning_Kind of the Object by a
      --  Task_Instance.

      procedure Check_Concurrent_Accesses_To_Entries
        (Entry_Callers : Name_To_Name_Lists.Map)
      with Pre => not Entry_Callers.Is_Empty;
      --  Emits a message in case there are more concurrent accesses to an
      --  entry than allowed.

      procedure Record_Ownership (Owning_Kind : Tasking_Owning_Kind;
                                  Object      : Entity_Name;
                                  Task_Type   : Entity_Name);
      --  Records an ownership of an Object by a Task_Type

      procedure Report_Violations (Object     : Entity_Name;
                                   Owners     : Task_Multisets.Set;
                                   Msg_Object : String;
                                   Msg_Owner  : String;
                                   SRM_Ref    : String);
      --  Emit checks about ownership violations

      ---------------------
      -- Msg_Attach_Node --
      ---------------------

      function Msg_Attach_Node
        (Task_Name   : Entity_Name;
         Object_Name : Entity_Name)
         return Entity_Id
      is
         Task_Node : constant Entity_Id := Find_Entity (Task_Name);

      begin
         if Present (Task_Node) then
            return Task_Node;
         else
            declare
               Object_Node : constant Entity_Id := Find_Entity (Object_Name);
            begin
               if Present (Object_Node) then
                  return Object_Node;
               else
                  return Defining_Entity (Unit (GNAT_Root));
               end if;
            end;
         end if;
      end Msg_Attach_Node;

      ---------------------
      -- Check_Ownership --
      ---------------------

      procedure Check_Ownership (Owning_Kind : Simple_Owning_Kind)
      is
         Msg : constant String :=
           (case Owning_Kind is
               when Suspends_On =>
                  "multiple tasks might suspend on suspension object &",
               when Unsynch_Accesses =>
                  "possible data race when accessing variable &");
         --  Main error message

         SRM_Ref : constant String :=
           (if Owning_Kind = Suspends_On
            then "9(11)"
            else "");
         --  Reference to SPARK RM for non-obvious verification rules

         Owned_Objects : Name_To_Name_Lists.Map renames
           Object_Owners (Owning_Kind);

      --  Start of processing for Check_Ownership

      begin
         for C in Owned_Objects.Iterate loop
            declare
               Object : Entity_Name renames Name_To_Name_Lists.Key (C);

               Owner_Types : Name_Lists.List renames Owned_Objects (C);

               First_Task_Type_Objects : Task_Multisets.Set renames
                 Task_Instances (Owner_Types.First_Element);

               Msg_Object : constant Entity_Name :=
                 (if GG_Is_Constituent (Object) and then
                      (for all Const of
                          Get_Constituents (GG_Encapsulating_State (Object))
                       => Owned_Objects.Contains (Const))
                  then GG_Encapsulating_State (Object)
                  else Object);
               --  If Owned_Objects contains all the constituents of a state
               --  abstraction then we issue the message only for the state
               --  abstraction.

            begin
               --  Violation occurs when the resource is accessed by:
               --  * instances of several task types
               --  * several objects of the same task type
               --  * a single object of a single task type, but with several
               --    instances of that type (e.g. array or record whose
               --    components are tasks).
               if Owner_Types.Length > 1
                    or else
                  First_Task_Type_Objects.Length > 1
                    or else
                  First_Task_Type_Objects.First_Element.Instances /= 1
               then
                  declare
                     Owners : Task_Multisets.Set;

                  begin
                     for Task_Type of Owner_Types loop
                        Owners.Union (Task_Instances (Task_Type));
                     end loop;

                     Report_Violations (Object     => Msg_Object,
                                        Owners     => Owners,
                                        Msg_Object => Msg,
                                        Msg_Owner  => "with task &",
                                        SRM_Ref    => SRM_Ref);
                  end;
               end if;
            end;
         end loop;
      end Check_Ownership;

      ------------------------------------------
      -- Check_Concurrent_Accesses_To_Entries --
      ------------------------------------------

      procedure Check_Concurrent_Accesses_To_Entries
        (Entry_Callers : Name_To_Name_Lists.Map)
      is
         Has_Restriction_No_Entry_Queue : constant Boolean :=
           Restriction_Active (No_Entry_Queue);
         --  Set to True if the restriction No_Entry_Queue is active

         Has_Restriction_Max_Entry_Queue_Length : constant Boolean :=
           Restriction_Active (Max_Entry_Queue_Length)
             or else
           Restriction_Active (Max_Entry_Queue_Depth);
         --  Set to True iff either the restrictions Max_Entry_Queue_Length or
         --  Max_Entry_Queue_Depth are active.

         Max_Entry_Queue_Len : constant Nat :=
           Nat (Restrictions.Value (Max_Entry_Queue_Length));
         --  Value of the configuration pragma Max_Entry_Queue_Length
         --  (zero if it is not present).

      begin
         --  Iterate over entry objects
         for Obj in Entry_Callers.Iterate loop
            declare
               use Max_Queue_Lenghts_Maps;

               Number_Of_Accesses : Nat := 0;
               --  Counts the number of accesses to the current entry object

               Current_Entry : Entity_Name renames
                 Name_To_Name_Lists.Key (Obj);
               --  Entry under analysis

               Max_Queue_Length : constant Nat :=
                 Max_Queue_Lengths (Current_Entry);
               --  Value of the pragma Max_Queue_Length attached to
               --  Current_Entry (zero if it is not present).

               Strongest_Restriction : constant Nat :=
                 (if Has_Restriction_Max_Entry_Queue_Length
                  and then Max_Queue_Length > 0
                  then Int'Min (Max_Queue_Length, Max_Entry_Queue_Len)
                  else Int'Max (Max_Queue_Length, Max_Entry_Queue_Len));
               --  Maximum number of tasks that can queue on the Current_Entry.
               --  If both Max_Queue_Length and Max_Entry_Queue_Len are
               --  positive we select the minimum, otherwise the maximum.

               Current_Max_Queue_Length : constant Nat :=
                 (if Has_Restriction_No_Entry_Queue
                  then 1
                  else Strongest_Restriction);
               --  This enforces the number of tasks that can queue on an entry
               --  to be 1 in case the restriction No_Entry_Queue is active.

               function Msg return String;
               --  Returns the error message to print together with the
               --  violated restriction

               ---------
               -- Msg --
               ---------

               function Msg return String is
                  Violated_Restriction : constant String :=
                    (if Has_Restriction_No_Entry_Queue
                     then "(restriction No_Entry_Queue active)"
                     elsif Has_Restriction_Max_Entry_Queue_Length
                       and then Max_Entry_Queue_Len = Current_Max_Queue_Length
                     then "(Max_Entry_Queue_Length =" &
                       Current_Max_Queue_Length'Img & ")"
                     else "(Max_Queue_Length =" &
                       Current_Max_Queue_Length'Img & ")");

               begin
                  return
                    ("more tasks than allowed might queue on protected " &
                       "entry & " & Violated_Restriction);
               end Msg;

               --  Local variables

               Queueing_Tasks : Task_Multisets.Set;
               --  Tasks that are queueing on the Current_Entry

            begin
               if Current_Max_Queue_Length > 0 then
                  --  Iterate over task types calling Current_Entry
                  for Task_Type of Entry_Callers (Obj) loop

                     for Task_Object of Task_Instances (Task_Type) loop
                        --  If the exact number of instances is not known
                        --  then assume the worst case, i.e. a value that
                        --  will trigger a SPARK violation (see declaration
                        --  of Task_Object type in Flow_Generated_Globals.ads).
                        if Task_Object.Instances = -1 then
                           Number_Of_Accesses := Current_Max_Queue_Length + 1;
                        else
                           Number_Of_Accesses := Number_Of_Accesses +
                             Task_Object.Instances;
                        end if;
                     end loop;

                     Queueing_Tasks.Union (Task_Instances (Task_Type));

                  end loop;

                  --  Emit a check if the number of concurrent accesses to
                  --  Current_Entry is greater than the allowed (from pragmas)
                  --  queue length.
                  if Number_Of_Accesses > Current_Max_Queue_Length then
                     Report_Violations (Object     => Current_Entry,
                                        Owners     => Queueing_Tasks,
                                        Msg_Object => Msg,
                                        Msg_Owner  => "task & is queueing",
                                        SRM_Ref    => "9(11)");
                  end if;
               end if;
            end;
         end loop;
      end Check_Concurrent_Accesses_To_Entries;

      ----------------------
      -- Record_Ownership --
      ----------------------

      procedure Record_Ownership (Owning_Kind : Tasking_Owning_Kind;
                                  Object      : Entity_Name;
                                  Task_Type   : Entity_Name)
      is
         Position : Name_To_Name_Lists.Cursor;
         Inserted : Boolean;

         Owners : Name_To_Name_Lists.Map renames Object_Owners (Owning_Kind);

      begin
         Owners.Insert (Key      => Object,
                        Position => Position,
                        Inserted => Inserted);

         Owners (Position).Append (Task_Type);
      end Record_Ownership;

      -----------------------
      -- Report_Violations --
      -----------------------

      procedure Report_Violations (Object     : Entity_Name;
                                   Owners     : Task_Multisets.Set;
                                   Msg_Object : String;
                                   Msg_Owner  : String;
                                   SRM_Ref    : String)
      is
         Msg_Node : constant Entity_Id :=
           Msg_Attach_Node (Task_Name   => Owners.First_Element.Name,
                            Object_Name => Object);

         Severity : constant Check_Kind := High_Check_Kind;
         --  Severity of the error messages

         Dummy : Boolean;
         --  Dummy variable needed for Error_Msg_Flow

      begin
         Error_Msg_Flow
           (E            => Msg_Node,
            N            => Msg_Node,
            Suppressed   => Dummy,
            Severity     => Severity,
            Tag          => Concurrent_Access,
            Msg          => Msg_Object,
            F1           => Magic_String_Id (Object),
            SRM_Ref      => SRM_Ref,
            Continuation => False);

         --  Print all the queueing tasks objects that we found
         for Task_Obj of Owners loop
            Error_Msg_Flow
              (E            => Msg_Node,
               N            => Msg_Node,
               Suppressed   => Dummy,
               Severity     => Severity,
               Tag          => Concurrent_Access,
               Msg          => Msg_Owner,
               F1           => Magic_String_Id (Task_Obj.Name),
               Continuation => True);
         end loop;
      end Report_Violations;

   --  Start of processing for Check_Concurrent_Accesses

   begin
      --  Invert mapping read from the ALI files:
      --    from {task types -> objects}
      --      to {objects -> task types}
      for C in Task_Instances.Iterate loop
         declare
            This_Task_Type : Entity_Name renames Task_Instances_Maps.Key (C);

         begin
            for Owning_Kind in Tasking_Owning_Kind loop
               for Obj of Tasking_Objects (Owning_Kind, This_Task_Type) loop
                  Record_Ownership (Owning_Kind => Owning_Kind,
                                    Object      => Obj,
                                    Task_Type   => This_Task_Type);
               end loop;
            end loop;
         end;
      end loop;

      --  First check simple ownerships, then entry ownerships

      for Owning_Kind in Simple_Owning_Kind loop
         Check_Ownership (Owning_Kind);
      end loop;

      declare
         Entry_Callers : Name_To_Name_Lists.Map renames
           Object_Owners (Entry_Calls);
         --  Mapping from entry objects to task types that call them

      begin
         if not Entry_Callers.Is_Empty then
            Check_Concurrent_Accesses_To_Entries (Entry_Callers);
         end if;
      end;

   end Check_Concurrent_Accesses;

   --------------------------------
   -- Check_CAE_In_Preconditions --
   --------------------------------

   procedure Check_CAE_In_Preconditions (FA : in out Flow_Analysis_Graphs) is

      Preconditions : Node_Lists.List;

      Globals : Global_Flow_Ids;

   begin
      --  We only perform this check on protected operations
      if not Is_Protected_Operation (FA.Analyzed_Entity) then
         return;
      end if;

      Preconditions := Get_Precondition_Expressions (FA.Analyzed_Entity);

      --  Populate global sets
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.S_Scope,
                   Classwide  => False,
                   Globals    => Globals);

      --  Add Proof_Ins to Reads
      Globals.Inputs.Union (Globals.Proof_Ins);

      for Precondition of Preconditions loop
         declare
            VU : constant Flow_Id_Sets.Set :=
              Get_Variables (Precondition,
                             Scope                => FA.S_Scope,
                             Fold_Functions       => False,
                             Use_Computed_Globals => True);
            --  The above set contains all variables used in the precondition.
         begin
            for Var of VU loop
               if Globals.Inputs.Contains (Change_Variant (Var, In_View))
                 and then not Is_Constant_After_Elaboration (Var)
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "variable & cannot be referenced in " &
                                 "precondition of protected operation &",
                     Severity => High_Check_Kind,
                     N        => Precondition,
                     F1       => Var,
                     F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                     SRM_Ref  => "9(10)",
                     Tag      => Reference_To_Non_CAE_Variable);
               end if;
            end loop;
         end;
      end loop;
   end Check_CAE_In_Preconditions;

   --------------------------
   -- Check_Elaborate_Body --
   --------------------------

   procedure Check_Elaborate_Body (FA : in out Flow_Analysis_Graphs)
   is
      use Flow_Graphs;

      Visible_Vars : Flow_Id_Sets.Set;

      procedure Visitor (V  :     Vertex_Id;
                         TV : out Simple_Traversal_Instruction);
      --  Emit a high check for all publically visible variables modified at
      --  this vertex.

      -------------
      -- Visitor --
      -------------

      procedure Visitor (V  :     Vertex_Id;
                         TV : out Simple_Traversal_Instruction)
      is
         K   : Flow_Id renames FA.PDG.Get_Key (V);
         Atr : V_Attributes renames FA.Atr (V);

         F : constant Flow_Id := (if Present (K)
                                  then K
                                  else Atr.Call_Vertex);
         --  This is the Flow_Id that we are interested in to check which
         --  variables are used. If the current has a key then it is that key,
         --  if not it is the call vertex. It could be Null_Flow_Id if there is
         --  none of the above.

      begin
         TV := Continue;

         --  Only check nodes in the body

         if Present (F)
           and then F.Kind = Direct_Mapping
           and then Get_Flow_Scope (F.Node).Part = Body_Part
         then
            for Var of Visible_Vars loop
               if Atr.Variables_Defined.Contains (Var) then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "modification of & in elaboration " &
                                 "requires Elaborate_Body on package &",
                     Severity => High_Check_Kind,
                     N        => Error_Location (FA.PDG, FA.Atr, V),
                     F1       => Var,
                     F2       => Direct_Mapping_Id (FA.Spec_Entity),
                     SRM_Ref  => "7.7.1(5)",
                     Tag      => Pragma_Elaborate_Body_Needed,
                     Vertex   => V);
               end if;
            end loop;
         end if;
      end Visitor;

   --  Start of processing for Check_Elaborate_Body

   begin
      --  We only check variables that we claim to initialize (either because
      --  we said so or because flow thinks so), since otherwise their use will
      --  be flagged as a potentially uninitialized read.

      for C in Parse_Initializes (FA.Spec_Entity, FA.S_Scope).Iterate loop
         declare
            Var : Flow_Id renames Dependency_Maps.Key (C);
         begin
            if Present (Var) then
               declare
                  Obj : constant Entity_Id := Get_Direct_Mapping_Id (Var);
                  pragma Assert (Ekind (Obj) in E_Abstract_State
                                              | E_Variable
                                              | E_Constant);

               begin
                  if Get_Flow_Scope (Declaration_Node (Obj)).Part in
                      Visible_Part | Private_Part
                    and then Ekind (Obj) /= E_Constant
                    and then Is_Initialized_At_Elaboration (Obj, FA.S_Scope)
                  then
                     Visible_Vars.Insert (Var);
                  end if;
               end;
            end if;
         end;
      end loop;

      FA.PDG.DFS (Start         => FA.Start_Vertex,
                  Include_Start => False,
                  Visitor       => Visitor'Access);
   end Check_Elaborate_Body;

   ----------------------------------
   -- Check_Terminating_Annotation --
   ----------------------------------

   procedure Check_Terminating_Annotation (FA : in out Flow_Analysis_Graphs) is
   begin
      if Has_Terminate_Annotation (FA.Spec_Entity) then
         declare
            Not_Proved : constant Boolean :=
              Is_Potentially_Nonreturning_Internal (FA.Spec_Entity);

            Msg : constant String :=
              (if Not_Proved
               then "subprogram & might not terminate, " &
                    "terminating annotation could be incorrect"
               else "subprogram & will terminate, " &
                    "terminating annotation has been proved");

            Severity : constant Msg_Severity :=
              (if Not_Proved
               then Medium_Check_Kind
               else Info_Kind);

         begin
            Error_Msg_Flow (FA       => FA,
                            Msg      => Msg,
                            Severity => Severity,
                            N        => FA.Spec_Entity,
                            F1       => Direct_Mapping_Id (FA.Spec_Entity),
                            Tag      => Subprogram_Termination);
         end;
      end if;
   end Check_Terminating_Annotation;

   -----------------------
   -- Check_Termination --
   -----------------------

   procedure Check_Termination (FA : in out Flow_Analysis_Graphs) is
   begin
      if Is_Potentially_Nonreturning (FA.Spec_Entity) then
         Error_Msg_Flow (FA       => FA,
                         Msg      => "subprogram & might not terminate",
                         Severity => Warning_Kind,
                         N        => FA.Spec_Entity,
                         F1       => Direct_Mapping_Id (FA.Spec_Entity));
      else
         --  In case a check has been raised with the
         --  Check_Terminating_Annotation then we do not emit the info message.
         if not (Has_Terminate_Annotation (FA.Spec_Entity)
                 and then
                 Is_Potentially_Nonreturning_Internal (FA.Spec_Entity))
         then
            Error_Msg_Flow (FA       => FA,
                            Msg      => "subprogram & will terminate",
                            Severity => Info_Kind,
                            N        => FA.Spec_Entity,
                            F1       => Direct_Mapping_Id (FA.Spec_Entity));
         end if;
      end if;
   end Check_Termination;

   ---------------------------------------
   -- Check_State_Volatility_Escalation --
   ---------------------------------------

   procedure Check_State_Volatility_Escalation
     (FA : in out Flow_Analysis_Graphs)
   is
      function To_String (P : Volatile_Pragma_Id) return String
      is (case P is
          when Pragma_Async_Readers    => "Async_Readers",
          when Pragma_Async_Writers    => "Async_Writers",
          when Pragma_Effective_Reads  => "Effective_Reads",
          when Pragma_Effective_Writes => "Effective_Writes");
   begin
      --  We check all states of the current package, for all volatility
      --  aspects...
      if Has_Non_Null_Abstract_State (FA.Spec_Entity) then
         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            for Property in Volatile_Pragma_Id loop

               --  We only check if the state *does not* have a certain aspect
               if not Has_Volatile (State)
                 or else not Has_Volatile_Property (State, Property)
               then
                  --  And for each aspect we do not have, we make sure all
                  --  (non-null) constituents also do not have it.

                  if Has_Non_Null_Refinement (State) then
                     for Constituent of Iter (Refinement_Constituents (State))
                     loop
                        if Has_Volatile (Constituent)
                          and then
                            Has_Volatile_Property (Constituent, Property)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "& cannot be a constituent of & "
                              & "(which lacks volatile property "
                              & To_String (Property) & ")",
                              Severity => Error_Kind,
                              N        => Constituent,
                              F1       => Direct_Mapping_Id (Constituent),
                              F2       => Direct_Mapping_Id (State));
                        end if;
                     end loop;
                  end if;
               end if;
            end loop;

         end loop;
      end if;
   end Check_State_Volatility_Escalation;

end Flow.Analysis;
