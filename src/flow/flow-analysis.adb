------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2025, Capgemini Engineering              --
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

with Atree;                       use Atree;
with Lib;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Output;                      use Output;
with Restrict;                    use Restrict;
with Rident;                      use Rident;
with Sem_Aggr;
with Sem_Aux;                     use Sem_Aux;
with Sem_Prag;
with Sem_Type;                    use Sem_Type;
with Sem_Warn;                    use Sem_Warn;
with Sinfo.Utils;                 use Sinfo.Utils;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with Stand;                       use Stand;

with Common_Iterators;            use Common_Iterators;
with SPARK_Frame_Conditions;      use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with SPARK_Util;                  use SPARK_Util;
with VC_Kinds;                    use VC_Kinds;

with Errout_Wrapper;              use Errout_Wrapper;
with Flow.Analysis.Antialiasing;
with Flow.Analysis.Sanity;
with Flow_Classwide;
with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Refinement;                use Flow_Refinement;
with Flow.Slice;                     use Flow.Slice;
with Flow_Utility;                   use Flow_Utility;
with Flow_Utility.Initialization;    use Flow_Utility.Initialization;

package body Flow.Analysis is

   Debug_Trace_Depends : constant Boolean := False;
   --  Enable this to show the specified and computed dependency relation

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Defines_Async_Reader_Var
     (FA : Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id)
      return Boolean;
   --  Returns True if vertex V defines some variable that has property
   --  Async_Readers set.

   function Dependency_Path (FA      : Flow_Analysis_Graphs;
                             Inputs  : Flow_Id_Sets.Set;
                             Outputs : Flow_Id_Sets.Set)
                             return Vertex_Sets.Set
   with Pre  => not Outputs.Is_Empty
                  and then
                (for all Input of Inputs => Input.Variant = Normal_Use)
                  and then
                (for all Output of Outputs => Output.Variant = Normal_Use),
        Post => (for all V of Dependency_Path'Result =>
                   FA.Atr (V).Is_Program_Node);
   --  Finds the shortest path in the PDG graph connecting any initial vertex
   --  for Inputs with any vertex that defines a variable from Outputs. Returns
   --  the vertices in this path (Inputs and Outputs excluded).

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
   --  as a substitute for a missing Refined_Global/Global.
   --
   --  ??? in some calls to this routine the F is a constituent while the
   --  contract references its abstract state; should be fixed either in
   --  Find_Global or in its callers.

   function Get_Initial_Vertex (G : Flow_Graphs.Graph;
                                F : Flow_Id)
                                return Flow_Graphs.Vertex_Id
   with Pre  => F.Variant = Normal_Use,
        Post => G.Get_Key (Get_Initial_Vertex'Result).Variant in
                   Initial_Value | Initial_Grouping;
   --  Returns the vertex id which represents the initial value for F

   function Is_Param_Of_Null_Procedure (E : Entity_Id) return Boolean
   with Pre => Nkind (E) in N_Entity;
   --  Returns True iff E is a parameter of a null procedure

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
   with Pre => Ekind (FA.Spec_Entity) = E_Procedure
               and then not Has_Effects (FA);
   --  Issue a warning if the subprogram is considered to have no effects

   -----------------
   -- Has_Effects --
   -----------------

   function Has_Effects (FA : Flow_Analysis_Graphs) return Boolean is
     (FA.Kind = Kind_Task
      or else
        (for some V of FA.CFG.Get_Collection (FA.End_Vertex,
                                              Flow_Graphs.Out_Neighbours)
         => FA.Atr (V).Is_Export));

   ------------------------------
   -- Defines_Async_Reader_Var --
   ------------------------------

   function Defines_Async_Reader_Var
     (FA : Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id)
      return Boolean
   is
     (for some Var_Def of FA.Atr (V).Variables_Defined =>
        Has_Async_Readers (Var_Def));

   ---------------------
   -- Dependency_Path --
   ---------------------

   function Dependency_Path (FA      : Flow_Analysis_Graphs;
                             Inputs  : Flow_Id_Sets.Set;
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
         Atr : V_Attributes renames FA.Atr (V);
      begin
         --  If object is written in a program statement or the path goes
         --  through such a statement, we pick its vertex directly.

         if Atr.Is_Program_Node then
            Vertices.Insert (V);

         --  If it is written as a subprogram call parameter, we pick the
         --  vertex of the call statement.

         elsif Atr.Is_Parameter
           or else Atr.Is_Global_Parameter
           or else Atr.Is_Implicit_Parameter
         then
            Vertices.Include (FA.PDG.Get_Vertex (Atr.Call_Vertex));
         end if;
      end Add_Loc;

      ----------------------
      -- Are_We_There_Yet --
      ----------------------

      procedure Are_We_There_Yet
        (V           : Flow_Graphs.Vertex_Id;
         Instruction : out Flow_Graphs.Traversal_Instruction)
      is
         Atr : V_Attributes renames FA.Atr (V);
      begin
         if (for some Var of Atr.Variables_Defined => Outputs.Contains (Var))
         then
            Instruction := Flow_Graphs.Found_Destination;
         else
            Instruction := Flow_Graphs.Continue;
         end if;
      end Are_We_There_Yet;

   --  Start of processing for Dependency_Path

   begin
      for Input of Inputs loop
         FA.PDG.Shortest_Path
           (Start         => Get_Initial_Vertex (FA.PDG, Input),
            Allow_Trivial => False,
            Search        => Are_We_There_Yet'Access,
            Step          => Add_Loc'Access);

         if not Vertices.Is_Empty then
            return Vertices;
         end if;
      end loop;

      --  ??? This should not happen, but this routine is broken when it comes
      --  to initialization of constituents declared in private child packages.

      return Vertex_Sets.Empty_Set;
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
      --  Suppress the warning for subprograms that are:
      --  * main, because they often have no data flow effects
      --  * do not return, because that is a kind of effect
      --  * raise exception, because that is a kind of effect as well
      --  * have explicit Global => null, because the lack of effects is clear
      --  * are ghost, because they often only check assertions
      --  * null procedures

      if not FA.Is_Main
        and then not Is_Possibly_Nonreturning_Procedure (FA.Spec_Entity)
        and then not Has_Exceptional_Contract (FA.Spec_Entity)
        and then not Has_User_Supplied_Globals (FA.Spec_Entity)
        and then not Is_Ghost_Entity (FA.Spec_Entity)
        and then not
          (Present (Subprogram_Body (FA.Spec_Entity))
            and then Was_Null_Procedure (Subprogram_Body (FA.Spec_Entity)))
      then
         Error_Msg_Flow
           (FA       => FA,
            Msg      => "subprogram & " & "has no effect",
            N        => FA.Spec_Entity,
            F1       => Direct_Mapping_Id (FA.Spec_Entity),
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
         --  Ignore deep delta choices, because they are too complicated and
         --  this routine merely determines location for the error message.

         if Nkind (N) in N_Selected_Component | N_Indexed_Component
           and then Nkind (Parent (N)) = N_Component_Association
           and then Is_List_Member (N)
           and then List_Containing (N) = Choices (Parent (N))
           and then Sem_Aggr.Is_Deep_Choice (N, Etype (Parent (Parent (N))))
         then
            return Skip;

         --  Identifier appearing as a choice in a component association is not
         --  really an expression (except when used as an index of an array
         --  component association). We process such identifiers while
         --  recursively traversing record aggregates.

         elsif Nkind (N) = N_Identifier
           and then Nkind (Parent (N)) = N_Component_Association
           and then Is_List_Member (N)
           and then List_Containing (N) = Choices (Parent (N))
           and then not Is_Array_Type (Etype (Parent (Parent (N))))
         then
            pragma Assert (Ekind (Entity (N)) in E_Component | E_Discriminant);

            --  Identifier as a choice in component_association occurs within
            --  an aggregate.

            pragma Assert
              (Nkind (Parent (Parent (N))) in N_Aggregate | N_Delta_Aggregate);

            return OK;

         --  Likewise for the selector_name of a selected_component

         elsif Nkind (N) = N_Identifier
           and then Nkind (Parent (N)) = N_Selected_Component
           and then N = Selector_Name (Parent (N))
         then
            --  Identifier denotes either a component/discriminant or a
            --  protected function/procedure/entry.

            pragma Assert
              (declare
                 E : constant Entity_Id := Entity (N);
               begin
                 Ekind (E) in E_Component | E_Discriminant
                   or else
                 (Is_Subprogram_Or_Entry (E)
                    and then
                  Ekind (Sinfo.Nodes.Scope (E)) = E_Protected_Type));
            return OK;

         elsif Nkind (N) in N_Subprogram_Call
                       | N_Entry_Call_Statement
                       | N_Expanded_Name
                       | N_Identifier
                       | N_Selected_Component
         then
            declare
               Expr_Vars : constant Flow_Id_Sets.Set :=
                 Get_All_Variables (N,
                                    Scope                => Scope,
                                    Target_Name          => Null_Flow_Id,
                                    Assume_In_Expression => False,
                                    Use_Computed_Globals => True);
               --  ??? Setting Target_Name to Null_Flow_Id is dubious here, but
               --  this First_Variable_Use routine is dubious itself. Anyway,
               --  this routine is only for error-reporting on illegal code.

            begin
               if (if Precise
                   then Expr_Vars.Contains (Var_Tgt)
                   else To_Entire_Variables (Expr_Vars).Contains (Var_Tgt))
               then
                  First_Use := N;
                  --  ??? Returning OK won't actually pick up the "first" use
                  --  of the variable in an expression, however it behaves
                  --  more intuitively with regard to subprogram parameters.
                  --  Returning Abandon here instead will tend to pick up
                  --  the first occurrence when the variable is found in an
                  --  expression, which is more intuitive for expressions but
                  --  less so in other cases.
                  return OK;
               else
                  return Skip;
               end if;
            end;

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
               --  ??? The object might appear in the LHS of the assignment,
               --  e.g. in the array index expressions, but we only search on
               --  the RHS to better locate checks on self-assignment of
               --  uninitialized objects.

               Search_Under := Expression (N);

            when N_Case_Statement =>
               Search_Under := Expression (N);

            when N_If_Statement
               | N_Elsif_Part
            =>
               Search_Under := Condition (N);

            when N_Loop_Statement =>
               Search_Under := Iteration_Scheme (N);

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

      First_Use : Node_Id := FA.Spec_Entity;

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
               First_Use := Atr.Error_Location;
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

   function Is_Dummy_Call (N : Node_Id; Scop : Flow_Scope) return Boolean
   with Pre => Nkind (N) in N_Subprogram_Call | N_Entry_Call_Statement;
   --  Returns True iff N is a call to subprogram with no parameters
   --  whatsoever (i.e. no formal parameters, no implicit parameters and no
   --  globals). Such a subprogram doesn't read or write anything, so from
   --  the flow analysis point of view it is equivalent to a null statement.
   --
   --  We prefer to warn about this once, when analysing that subprogram
   --  itself and not everytime it is called.

   -------------------
   -- Is_Dummy_Call --
   -------------------

   function Is_Dummy_Call (N : Node_Id; Scop : Flow_Scope) return Boolean is
      E : constant Entity_Id := Get_Called_Entity (N);

      Globals : Global_Flow_Ids;

   begin
      --  The implicit formal parameter is an effect

      if Ekind (Scope (E)) = E_Protected_Type then
         return False;

      --  Any explicit formal parameter is an effect

      elsif Present (First_Formal (E)) then
         return False;

      --  Globals on access-to-subprogram are not allowed

      elsif Ekind (E) = E_Subprogram_Type then
         return True;

      --  Any global parameter is an effect

      else
         Get_Globals (Subprogram          => E,
                      Scope               => Scop,
                      Classwide           => False,
                      Globals             => Globals,
                      Use_Deduced_Globals => True);

         return Globals.Proof_Ins.Is_Empty
           and then Globals.Inputs.Is_Empty
           and then Globals.Outputs.Is_Empty;
      end if;
   end Is_Dummy_Call;

   --------------------------------
   -- Is_Param_Of_Null_Procedure --
   --------------------------------

   function Is_Param_Of_Null_Procedure (E : Entity_Id) return Boolean is
   begin
      if Is_Formal (E) then
         declare
            Subp : constant Entity_Id := Scope (E);
         begin
            return Ekind (Subp) = E_Procedure
              and then Present (Subprogram_Body (Subp))
              and then Was_Null_Procedure (Subprogram_Body (Subp));
         end;
      else
         return False;
      end if;
   end Is_Param_Of_Null_Procedure;

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
         Sanity.Check_Illegal_Writes_And_All_Variables_Known'Access,
         Sanity.Check_Side_Effects_In_Protected_Functions'Access);
   begin
      for C of Sanity_Checks loop
         C (FA, Sane);
         exit when not Sane;
      end loop;
   end Sanity_Check;

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

      function Is_Or_Belongs_To_Concurrent_Object
        (F : Flow_Id)
         return Boolean
      with Pre => F.Kind in Direct_Mapping | Record_Field;
      --  @param F is the Flow_Id that we want to check
      --  @return True iff F is or belongs to a concurrent object

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

      for V of FA.CFG.Get_Collection
        (FA.End_Vertex, Flow_Graphs.Out_Neighbours)
      loop
         declare
            F_Final : Flow_Id      renames FA.PDG.Get_Key (V);
            A_Final : V_Attributes renames FA.Atr (V);

            Written : Boolean;

         begin
            pragma Assert (F_Final.Variant = Final_Value);

            if A_Final.Is_Export
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
               pragma Assert (F_Final.Kind in Direct_Mapping | Record_Field);
               declare
                  Var : constant Entity_Id := Get_Direct_Mapping_Id (F_Final);

                  Is_In_Access_Parameter : constant Boolean :=
                    (Ekind (Var) = E_In_Parameter
                     and then Is_Access_Variable (Etype (Var)));
                  --  Mode IN Formal parameters of access-to-variable type can
                  --  be written and thus appear as exports (though they are
                  --  typically used without being written.)

               begin
                  --  We inhibit messages for non-global exports that:
                  --   * have been marked as unmodified, as unused or as
                  --     unreferenced,
                  --   * are/belong to a concurrent object
                  --   * are formal parameters of a subprogram with null
                  --     default defined in the formal part of a generic unit
                  --   * are formal parameters of a null procedure
                  --   * are instantiations of a generic procedure's 'IN'
                  --     parameter with an access type
                  --   * are first parameters of a borrowing traversal function
                  --     (which must be writable)
                  if Has_Pragma_Un (Var)
                    or else
                      Is_Or_Belongs_To_Concurrent_Object (F_Final)
                    or else Is_Param_Of_Null_Subp_Of_Generic (Var)
                    or else Is_Param_Of_Null_Procedure (Var)
                    or else
                      (Is_In_Access_Parameter
                       and then Is_Generic_Actual_Type (Etype (Var)))
                    or else
                     (Is_Borrowing_Traversal_Function (FA.Spec_Entity)
                      and then Var = First_Formal (FA.Spec_Entity))
                  then
                     null;
                  elsif not Written_Exports.Contains
                    (Entire_Variable (F_Final))
                  then
                     if Is_In_Access_Parameter then
                        declare
                           Typ       : constant Entity_Id :=
                             Directly_Designated_Type (Etype (Var));
                           E         : Entity_Id;
                           Report_Id : Flow_Id;
                        begin

                           --  If Var points to the completion of a type, then
                           --  we use the incomplete view in the message
                           --  (because the full view is flagged as internal).
                           if Present (Incomplete_View (Typ)) then
                              E := Incomplete_View (Typ);
                           else
                              E := Typ;
                           end if;

                           Report_Id := Direct_Mapping_Id
                             (if Comes_From_Source (E)
                                or else Is_Standard_Type (E)
                              then E
                              else Base_Type (E));
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "& is not modified, parameter type" &
                                " could be rewritten as 'access constant %'",
                              N        => Error_Location (FA.PDG, FA.Atr, V),
                              F1       => Entire_Variable (F_Final),
                              F2       => Report_Id,
                              Tag      => Inout_Only_Read,
                              Severity => Warning_Kind,
                              Vertex   => V);
                        end;
                     else
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
      with Pre => (if FA.Is_Generative then Unused_Globals.Is_Empty)
                    and then
                  Components_Are_Entire_Variables (Unused);
      --  Issue a warning on unused objects; the second parameter controls
      --  emitting messages on globals coming from a user-written contract.

      procedure Warn_On_Ineffective_Imports
        (Ineffective         : Flow_Id_Sets.Set;
         Ineffective_Globals : Node_Sets.Set)
      with Pre => (if FA.Is_Generative then Ineffective_Globals.Is_Empty)
                    and then
                  Components_Are_Entire_Variables (Ineffective);
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
         Key : Flow_Id renames FA.PDG.Get_Key (V);
         Atr : V_Attributes renames FA.Atr (V);

      begin
         return
           (case Key.Variant is
               when Final_Value => Atr.Is_Export,
               when Normal_Use  => Atr.Is_Exceptional_Branch
                                     or else
                                   Atr.Is_Assertion
                                     or else
                                   (Atr.Is_Callsite
                                      and then
                                    Is_Dummy_Call
                                      (Get_Direct_Mapping_Id (Key),
                                       FA.B_Scope))
                                     or else
                                   Defines_Async_Reader_Var (FA, V),
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
               Get_Depends (Subprogram => FA.Spec_Entity,
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
                       (Is_Bound (Var) or else Is_Discriminant (Var))
                         and then
                         not (Is_Constituent (Var)
                                or else Is_Implicit_Constituent (Var));
                     --  If this is an array bound or a discriminant that will
                     --  never be seen via its encapsulating abstract state,
                     --  then we only consider it if it is actually used. It is
                     --  OK to not explicitly use it.

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
               V      : constant Flow_Graphs.Vertex_Id :=
                 Get_Initial_Vertex (FA.PDG, F);
               Is_Var : constant Boolean := Is_Variable (F);
               --  Issue different messages for variables and constants

            begin
               if FA.Atr (V).Is_Global then
                  --  In generative mode we inhibit messages on globals
                  if not FA.Is_Generative then
                     declare
                        Repr : constant Entity_Id :=
                          Find_In (Unused_Globals, Get_Direct_Mapping_Id (F));
                        --  An entity that represents F in unused, user-written
                        --  Global/Depends items.

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
                              Tag      => Unused_Global,
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
                  --    of a generic unit
                  --  * the variable is a formal parameter of a null procedure
                  declare
                     E     : constant Entity_Id := Get_Direct_Mapping_Id (F);
                     E_Typ : constant Entity_Id := Etype (E);

                  begin
                     if Is_Concurrent_Type (E_Typ)
                       or else Is_Empty_Record_Type (E_Typ)
                       or else Has_Pragma_Un (E)
                       or else Has_Junk_Name (E)
                       or else Is_Param_Of_Null_Subp_Of_Generic (E)
                       or else Is_Param_Of_Null_Procedure (E)
                     then
                        null;

                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             (if Is_Var then "unused variable &"
                              else "unused &"),
                           N        => Error_Location (FA.PDG, FA.Atr, V),
                           F1       => F,
                           Tag      => Unused_Variable,
                           Severity => Warning_Kind,
                           Vertex   => V);
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
                        F2       => Direct_Mapping_Id (FA.Spec_Entity),
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
                        F2       => Direct_Mapping_Id (FA.Spec_Entity),
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
        or else Has_User_Supplied_Globals (FA.Spec_Entity)
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
      end if;
   end Find_Ineffective_Imports_And_Unused_Objects;

   ---------------------------------
   -- Find_Ineffective_Statements --
   ---------------------------------

   procedure Find_Ineffective_Statements (FA : in out Flow_Analysis_Graphs) is

      Reachable_Code : Vertex_Sets.Set;
      --  Reachable program nodes; we only warn about ineffective statements on
      --  live nodes and warn about all the other nodes as being unreachable.

      procedure Flag_Reachable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Flag the given node as reachable
      --  ??? This repeats a traversal in Find_Dead_Code

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

      function Null_Dependency_Assignment
        (V   : Flow_Graphs.Vertex_Id;
         Atr : V_Attributes)
         return Boolean
      with Pre => Atr.Is_Parameter or else Atr.Is_Global_Parameter;
      --  Returns True iff vertex V (whose attributes are Atr) represents
      --  an assignment to an OUT mode parameter or a global Output via a
      --  subprogram call and there is an explicit
      --  "Depends => (... => null)" contract for this parameter.

      function Other_Field_Is_Effective (V : Flow_Graphs.Vertex_Id)
                                         return Boolean;
      --  Returns True if V corresponds to an assignment to a record field
      --  that has been introduced by a record split and some of the fields
      --  is effective.

      --------------------
      -- Flag_Reachable --
      --------------------

      procedure Flag_Reachable
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         Atr : V_Attributes renames FA.Atr (V);
      begin
         if Atr.Is_Program_Node then
            Reachable_Code.Insert (V);
         end if;

         TV := (if Atr.Execution = Normal_Execution
                then Flow_Graphs.Continue
                else Flow_Graphs.Skip_Children);
      end Flag_Reachable;

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
                  V_Atr : V_Attributes renames FA.Atr (V);

                  Intersection : constant Flow_Id_Sets.Set :=
                    Vars_Defined and
                    (V_Atr.Variables_Defined - V_Atr.Variables_Used);

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

      -----------------------------
      -- Is_Final_Use_Any_Export --
      -----------------------------

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean
      is
         Key : Flow_Id renames FA.PDG.Get_Key (V);
         Atr : V_Attributes renames FA.Atr (V);

      begin
         return
           (case Key.Variant is
               when Final_Value => Atr.Is_Export,
               when Normal_Use  => Atr.Is_Exceptional_Branch
                                     or else
                                   Atr.Is_Assertion
                                     or else
                                   (Atr.Is_Callsite
                                      and then
                                    Is_Dummy_Call
                                      (Get_Direct_Mapping_Id (Key),
                                       FA.B_Scope))
                                     or else
                                   Defines_Async_Reader_Var (FA, V),
               when others      => False);
      end Is_Final_Use_Any_Export;

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

      --------------------------------
      -- Null_Dependency_Assignment --
      --------------------------------

      function Null_Dependency_Assignment
        (V   : Flow_Graphs.Vertex_Id;
         Atr : V_Attributes)
         return Boolean
      is
      begin
         --  Each vertex for an Out_View parameter has an edge coming from the
         --  vertex that represents the call statement itself.
         --
         --  We first check if there are no other incoming edges, which means
         --  there are no dependencies flowing into this parameter; then we
         --  check if this subprogram has an explicit Depends contract.

         return FA.PDG.In_Neighbour_Count (V) = 1
           and then
             Has_Depends
               (Get_Called_Entity
                  (Get_Direct_Mapping_Id
                     (Atr.Call_Vertex)));
      end Null_Dependency_Assignment;

      ------------------------------
      -- Other_Field_Is_Effective --
      ------------------------------

      function Other_Field_Is_Effective (V : Flow_Graphs.Vertex_Id)
                                         return Boolean
      is
         My_First_Field : constant Flow_Graphs.Vertex_Id :=
           FA.Atr (V).First_Field;
         Other_Field : Flow_Graphs.Vertex_Id;
      begin
         --  Vertices representing declaration of / assignment to a record
         --  object form a linear sequence in the CFG. We pick the first
         --  vertex from this sequence and traverse the sequence looking
         --  for a vertex that is effective.

         Other_Field := My_First_Field;

         --  This might be a simple declaration/assignment with no sequence
         --  (e.g. for a scalar object) or perhaps the sequence ended with
         --  no outgoing edges for some reason.

         while Other_Field /= Flow_Graphs.Null_Vertex loop

            --  Skip the current field

            if Other_Field = V then
               null;

            --  Check if this field comes from the same declaration/assignment

            elsif FA.Atr (Other_Field).First_Field = My_First_Field then
               if FA.PDG.Non_Trivial_Path_Exists
                 (Other_Field, Is_Final_Use_Any_Export'Access)
               then
                  return True;
               end if;

            --  Otherwise we are done

            else
               exit;
            end if;

            --  Proceed to the next field

            Other_Field := FA.CFG.Child (Other_Field);
         end loop;

         return False;
      end Other_Field_Is_Effective;

   --  Start of processing for Find_Ineffective_Statements

   begin
      if FA.Kind = Kind_Subprogram
        and then not Has_Effects (FA)
      then
         Warn_On_Subprogram_With_No_Effect (FA);
         return;
      end if;

      --  Discover live code
      FA.CFG.DFS (Start         => FA.Start_Vertex,
                  Include_Start => True,
                  Visitor       => Flag_Reachable'Access);

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : Flow_Id renames FA.PDG.Get_Key (V);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Atr.Is_Program_Node
              or else
                (Atr.Is_Parameter
                 and then Key.Variant = Out_View)
              or else
                (Atr.Is_Global_Parameter
                 and then Atr.Parameter_Formal.Variant = Out_View)
            then

               --  A vertex is ineffective if there is no path in the PDG to
               --  *any* final use vertex that is also an export.

               if
                 --  Basic check here
                 not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use_Any_Export'Access) and then

                 --  We only want to find ineffective statements within code
                 --  that is reachable; code that is unreachable is clearly
                 --  ineffective as well, but it gets its own warning.
                 Reachable_Code.Contains
                   (if Atr.Is_Program_Node
                    then V
                    else FA.PDG.Get_Vertex (Atr.Call_Vertex)) and then

                 --  Suppression for package initializations
                 not Atr.Is_Package_Initialization and then

                 --  If we analyse a package, we suppress this message if we
                 --  don't have an initializes clause *and* the given vertex
                 --  has an effect on any final use (export or otherwise).
                 (if FA.Kind = Kind_Package
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
                 --  some of the other fields is effective.
                 not Other_Field_Is_Effective (V) and then

                 --  Suppression for vertices that define a variable that has
                 --  Async_Readers set.
                 not Defines_Async_Reader_Var (FA, V) and then

                 --  Suppression for elaboration of nested packages
                 not Is_Package_Elaboration (V) and then

                 --  Suppression for ineffective statements caused by dead code
                 --  coming from constants with Warnings => Off
                 not Atr.Warnings_Off and then

                 --  Suppression for calls to subprograms with no effects
                 not (Atr.Is_Callsite
                        and then
                      Is_Dummy_Call (Get_Direct_Mapping_Id (Key), FA.B_Scope))

               then
                  declare
                     Mask : constant Vertex_Sets.Set := Find_Masking_Code (V);
                     N    : constant Node_Id := Error_Location (FA.PDG,
                                                                FA.Atr,
                                                                V);

                  begin
                     if Atr.Is_Parameter or Atr.Is_Global_Parameter then
                        if not Null_Dependency_Assignment (V, Atr) then
                           declare
                              Target : constant Flow_Id :=
                                (if Atr.Is_Parameter
                                 then
                                    Path_To_Flow_Id
                                      (Get_Direct_Mapping_Id
                                        (Atr.Parameter_Actual),
                                       FA.B_Scope)
                                 else Atr.Parameter_Formal);
                              --  ??? Path_To_Flow_Id was meant to be used
                              --  in a borrow checker, but it also works for
                              --  converting an assignable actual parameter.

                              pragma Assert
                                (if Present (Target)
                                 then Is_Easily_Printable (Target));

                              Callee : constant Flow_Id :=
                                Direct_Mapping_Id
                                  (Get_Called_Entity
                                     (Get_Direct_Mapping_Id
                                        (Atr.Call_Vertex)));

                           begin
                              if Present (Target) then
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Path     => Mask,
                                    Msg      => "& is set by &" &
                                                " but not used after the call",
                                    N        => N,
                                    F1       => Target,
                                    F2       => Callee,
                                    Tag      => Ineffective,
                                    Severity => Warning_Kind,
                                    Vertex   => V);
                              end if;
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

                        --  This warning is ignored for local constants

                        if not Constant_Present (N) then

                           if FA.Kind = Kind_Package
                             and then
                               Scope (Defining_Identifier (N)) = FA.Spec_Entity
                             and then
                                 No (Find_In_Initializes
                                       (Defining_Identifier (N)))
                           then

                              --  This is checked by Check_Initializes_Contract

                              null;

                           --  Ignore discriminants initialized at declarations
                           --  of constrained objects.

                           elsif (for all Def of Atr.Variables_Defined =>
                                     Is_Discriminant (Def))
                           then
                              --  Actually, we handle such discriminants are
                              --  initialized one-by-one and each in its own
                              --  vertex.
                              pragma Assert
                                (Atr.Variables_Defined.Length = 1);

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
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
         begin
            if Atr.Is_Original_Program_Node

              --  Suppress the warning on nodes in instances or inlined code

              and then Instantiation_Location (Sloc (Atr.Error_Location))
                       = No_Location

              --  Suppress the warning on nodes flagged with Warnings_Off
              --  (right now, it happens when the unreachable code comes from
              --  a statically known condition involving a constant with
              --  Warnings => Off).

              and then not Atr.Warnings_Off
            then
               Error_Msg_Flow (FA       => FA,
                               Msg      => "this statement is never reached",
                               Severity => Warning_Kind,
                               N        => Atr.Error_Location,
                               Tag      => VC_Kinds.Dead_Code,
                               Vertex   => V);
            end if;
         end;
      end loop;
   end Find_Dead_Code;

   -----------------------------------------
   -- Find_Use_Of_Uninitialized_Variables --
   -----------------------------------------

   procedure Find_Use_Of_Uninitialized_Variables
     (FA : in out Flow_Analysis_Graphs)
   is
      type Msg_Kind is (Unknown, Err);

      type Path_Vertices is record
         Start : Flow_Graphs.Vertex_Id;
         V_Use : Flow_Graphs.Vertex_Id;
      end record;
      --  End vertices of a definition-free path in the graph

      function Hash (Path : Path_Vertices) return Ada.Containers.Hash_Type;
      --  Hash function for Path_Vertices records

      package Path_To_Variables_Maps is new Ada.Containers.Hashed_Maps
       (Key_Type        => Path_Vertices,
        Element_Type    => Flow_Id_Sets.Set,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

      Err_Checks     : Path_To_Variables_Maps.Map;
      Unknown_Checks : Path_To_Variables_Maps.Map;
      --  Map definition-free paths to variables on which we need to emit Err
      --  (resp. Unknown) checks for uninitialization.

      procedure Emit_Check_Message
        (Var   : Flow_Id;
         Start : Flow_Graphs.Vertex_Id;
         V_Use : Flow_Graphs.Vertex_Id;
         Kind  : Msg_Kind)
      with Pre  => not Is_Internal (Var)
                   and then Start /= Flow_Graphs.Null_Vertex
                   and then V_Use /= Flow_Graphs.Null_Vertex;
      --  Produces an appropriately worded low/high message for variable Var
      --  and looks for a path without initialization linking Start to V_Use
      --  for it to be written in a tracefile.

      procedure Emit_Check_Messages
        (Kind            : Msg_Kind;
         Kind_Checks     : in out Path_To_Variables_Maps.Map;
         Non_Kind_Checks : in out Path_To_Variables_Maps.Map);
      --  Produces the appropriately worded check messages for the uses of
      --  uninitialized variables corresponding to the specified message Kind.
      --  Kind_Checks (resp. Non_Kind_Checks) is a shortcut for the map
      --  associated with Kind (resp. non Kind) checks. Check messages
      --  associated with individual subcomponents are compressed into one
      --  message associated with their enclosing object, iff all the
      --  subcomponents are uninitialized at a given point in the subprogram.
      --  The parts on which we need to emit checks are added to Kind_Checks
      --  not to traverse their type again while emitting non Kind checks.

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

      function Proved_Msg (Var : Flow_Id) return String
      with Pre => Var.Kind in Direct_Mapping | Magic_String;
      --  Returns message about initialization of Var

      procedure Scan_Children
        (Var                  : Flow_Id;
         V_Initial            : Flow_Graphs.Vertex_Id;
         Possibly_Initialized : Boolean;
         Visited              : in out Vertex_Sets.Set;
         OK                   : in out Boolean)
      with Pre  => Var.Variant = Normal_Use
                   and then V_Initial /= Flow_Graphs.Null_Vertex
                   and then (if not Is_Array (Var)
                             then not Possibly_Initialized
                               and then Visited.Is_Empty),
           Post => Vertex_Sets.Is_Subset (Subset => Visited'Old,
                                          Of_Set => Visited)
                   and then (if not OK'Old then not OK);
      --  Detect uses of Var, which is a not-yet-initialized object, by
      --  looking at the PDG vertices originating from V_Initial. For arrays
      --  this routine might be called recursively and then
      --  Possibly_Initialized is True iff some elements of the array have been
      --  written. Visited contains vertices that have been already examined;
      --  it is to prevent infinite recursive calls. If we detect a use of Var
      --  while uninitialized, then OK will become False; otherwise, it will be
      --  unmodified. If OK becomes False, a pair of end vertices of a
      --  definition-free path is mapped to Var in Err_Checks (resp.
      --  Unknown_Checks) if we need to emit an Err (resp. Unknown) check.

      function Is_Array (F : Flow_Id) return Boolean;
      --  Returns True iff F represents an array and thus requires special
      --  handling.

      function Is_Empty_Record_Object (F : Flow_Id) return Boolean;
      --  Returns True iff F is a record that carries no data

      function Is_Main_Global_Input (Atr : V_Attributes) return Boolean;
      --  Returns True iff FA is a main-like subprogram and the vertex whose
      --  attribute is Atr is a global input of FA.

      function Is_Initialized (F : Flow_Id; Atr : V_Attributes) return Boolean
      with Pre =>
        F.Variant = Initial_Value
          and then FA.Atr (FA.DDG.Get_Vertex (F)) = Atr;
      --  * If FA is a main-like subprogram and F a global input of FA, returns
      --    True if F it is initialized after elaboration of FA.
      --  * Otherwise, returns Atr.Is_Initialized.

      function Has_Relaxed_Initialization (F : Flow_Id) return Boolean;
      --  Returns True iff F is subject to Relaxed_Initialization aspect

      ------------------------
      -- Emit_Check_Message --
      ------------------------

      procedure Emit_Check_Message
        (Var   : Flow_Id;
         Start : Flow_Graphs.Vertex_Id;
         V_Use : Flow_Graphs.Vertex_Id;
         Kind  : Msg_Kind)
      is
         V_Key        : Flow_Id renames FA.PDG.Get_Key (V_Use);

         V_Initial    : constant Flow_Graphs.Vertex_Id :=
           Get_Initial_Vertex (FA.PDG, Var);

         V_Initial_Atr : V_Attributes renames FA.Atr (V_Initial);
         V_Start_Atr   : V_Attributes renames FA.Atr (Start);

         N                              : Node_Or_Entity_Id;
         Msg, Details, Explanation, Fix : Unbounded_String;
         Explanation_F1                 : Flow_Id;
         Fix_F1, Fix_F2                 : Flow_Id;
         --  Optional parameters for messages with the explanation and the fix,
         --  respectively.

         V_Goal       : Flow_Graphs.Vertex_Id;

         Is_Final_Use          : constant Boolean :=
           V_Key.Variant = Final_Value;
         Is_Global             : constant Boolean := V_Initial_Atr.Is_Global;
         Default_Init          : constant Boolean :=
           Var.Kind in Direct_Mapping | Record_Field
           and then Is_Default_Initialized (Var);
         Is_Function           : constant Boolean := Is_Function_Entity (Var);
         Is_Read_Global_Output : constant Boolean :=
           Kind = Err
           and then not Default_Init
           and then Is_Global
           and then not Is_Final_Use;

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
               A : V_Attributes renames FA.Atr (V);
            begin
               if (V = Start and then A.Is_Param_Havoc)
                 or else (V /= To and then F.Kind = Direct_Mapping)
               then
                  Path.Insert (V);
               end if;
            end Add_Loc;

         --  Start of processing for Mark_Definition_Free_Path

         begin
            FA.CFG.Shortest_Path (Start         => Start,
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

      --  Start of processing for Emit_Check_Message

      begin
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

         --  Assemble appropriate message for failed initialization. We deal
         --  with a bunch of special cases first, but if they don't trigger we
         --  create the standard message.

         if Is_Read_Global_Output then

            --  In case of a subprogram with an output global which is actually
            --  used as an input in its body, we emit dedicated messages.

            declare
               Msg : constant String :=
                 "either make & an input in the Global contract or " &
                 (if Has_Async_Readers (Var)
                  then "write to it before use"
                  else "initialize it before use");
            begin
               Error_Msg_Flow
                 (FA            => FA,
                  Msg           => "& is not an input in the " &
                    "Global contract of subprogram #",
                  Severity      => High_Check_Kind,
                  N             => N,
                  F1            => Var,
                  F2            =>
                    Direct_Mapping_Id (FA.Spec_Entity),
                  Tag           => Uninitialized,
                  Continuations =>
                    [Create (Substitute_Message (Msg, N, Var))]);
            end;

         else
            if Is_Function then
               Msg := To_Unbounded_String ("function & does not return on ");
--             if Has_Only_Infinite_Execution (Vertex) then
--                Append (Msg, "any path");
--             else
--                Append (Msg, "some paths");
--             end if;
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

                  --  Here we build the Details and Fix messages. In the first
                  --  branch of the if statement, we deal with a variable that
                  --  isn't initialized after elaboration of a package, but is
                  --  mentioned in the (generated or not) Initializes aspect of
                  --  said package, either directly or through an abstract
                  --  state.

                  if FA.Kind = Kind_Package then
                     if FA.Is_Generative then
                        Append (Details, "variable is mentioned in the " &
                                         "generated Initializes contract");
                     else
                        pragma Assert
                          (Var.Kind in Direct_Mapping | Record_Field);
                        declare
                           E          : constant Entity_Id :=
                             Get_Direct_Mapping_Id (Var);
                           Is_Visible : constant Boolean   :=
                             (if Ekind (E) = E_Abstract_State
                              then Scope (E) = FA.Spec_Entity
                              else List_Containing
                                     (Enclosing_Declaration (E)) =
                                   Visible_Declarations
                                     (Package_Specification (FA.Spec_Entity)));

                        begin
                           if Is_Visible then
                              Append (Details, "variable ");
                           else
                              Append (Details, "encapsulating state ");
                           end if;

                           Append (Details, "is mentioned in the Initializes "
                                   & "contract of the package "
                                   & "declaration");
                        end;
                     end if;

                     Append (Fix, "initialize & at declaration");
                     if Entity_Body_In_SPARK (FA.Spec_Entity) then
                        Append (Fix, " or in the package body statements");
                     end if;
                     Fix_F1 := Var;

                  --  We are dealing with an OUT parameter that is not
                  --  initialized on return. We suggest two fixes by default
                  --  and add a third one if the variable is a record part or
                  --  an array.

                  else
                     declare
                        Is_Record_Part_Or_Array : constant Boolean :=
                          Var.Kind = Record_Field
                          or else Is_Array (Var)
                          or else (Var.Kind = Direct_Mapping
                                   and then Var.Facet = Normal_Part
                                   and then
                                   Is_Record_Type
                                     (Get_Type (Var, FA.B_Scope)));

                     begin
                        --  Construction of the Details message
                        Append (Details, "OUT parameter should be ");
                        if Is_Record_Part_Or_Array then
                           Append (Details, "fully ");
                        end if;
                        Append (Details, "initialized on return");

                        --  First possible fix
                        Append (Fix, "initialize & on all paths");
                        Fix_F1 := Var;

                        --  Second possible fix

                        if not V_Start_Atr.Is_Param_Havoc then
                           if Is_Record_Part_Or_Array then
                              Append (Fix, ", ");
                           else
                              Append (Fix, " or ");
                           end if;
                           Append (Fix, "make & an IN OUT parameter");
                           Fix_F2 := Entire_Variable
                             (Change_Variant (Var, Normal_Use));
                        end if;

                        --  Third possible fix
                        if Is_Record_Part_Or_Array then
                           Append (Fix, " or annotate it with aspect "
                                   & "Relaxed_Initialization");
                        end if;
                     end;
                  end if;
               end if;
               if Is_Main_Global_Input (V_Initial_Atr) then
                  Append (Msg,
                          (case FA.Kind is
                              when Kind_Subprogram =>
                                " after elaboration of main program &",
                              when Kind_Task       =>
                                " before start of tasks of type &",
                              when others          =>
                                 raise Program_Error));
                  --  ??? this message should be tuned for interrupt handlers
               end if;
            end if;

            --  Add reason for check when starting vertex is a parameter havoc
            if V_Start_Atr.Is_Param_Havoc then
               Append (Explanation, "value of & is unknown following "
                                  & "exceptional exit");
               Explanation_F1 := Var;
            end if;

            declare
               Path : constant Vertex_Sets.Set :=
                 Mark_Definition_Free_Path (To  => V_Goal,
                                            Var => Var);
               Conts : Message_Lists.List;
            begin

               --  ??? only when Is_Final_Use ?
               if Is_Constituent (Var)
                 and then FA.Kind = Kind_Package
                 and then Present (FA.Initializes_N)
               then
                  Conts.Append
                    (Create
                       (Substitute_Message
                          ("initialization of & is specified @",
                           N  => N,
                           F1 => Direct_Mapping_Id
                             (Encapsulating_State
                                (Get_Direct_Mapping_Id (Var))),
                           F2 =>
                             Direct_Mapping_Id
                               (if From_Aspect_Specification (FA.Initializes_N)
                                then Corresponding_Aspect (FA.Initializes_N)
                                else FA.Initializes_N))));
               end if;

               Error_Msg_Flow
                 (FA            => FA,
                  Path          => Path,
                  Msg           => To_String (Msg),
                  Details       => To_String (Details),
                  Explanation   => To_String (Explanation),
                  Fix           => To_String (Fix),
                  N             => N,
                  F1            => Var,
                  F2            => Direct_Mapping_Id (FA.Spec_Entity),
                  EF1           => Explanation_F1,
                  FF1           => Fix_F1,
                  FF2           => Fix_F2,
                  Tag           => Uninitialized,
                  Severity      =>
                    (case Kind is
                        when Unknown => (if Default_Init
                                         then Low_Check_Kind
                                         else Medium_Check_Kind),
                        when Err     => (if Default_Init
                                         then Medium_Check_Kind
                                         else High_Check_Kind)),
                  Vertex        => V_Use,
                  Continuations => Conts);
            end;
         end if;
      end Emit_Check_Message;

      -------------------------
      -- Emit_Check_Messages --
      -------------------------

      procedure Emit_Check_Messages
        (Kind            : Msg_Kind;
         Kind_Checks     : in out Path_To_Variables_Maps.Map;
         Non_Kind_Checks : in out Path_To_Variables_Maps.Map)
      is
         procedure Compress_Checks
           (Path  : Path_Vertices;
            Var   : Flow_Id;
            Parts : in out Flow_Id_Sets.Set);
         --  Traverses the type of Var by calling itself recursively and puts
         --  in Parts either Var, if all its subcomponents are uninitialized at
         --  V_Use, or the uninitialized subcomponents of Var.

         ----------------------
         -- Compress_Checks --
         ----------------------

         procedure Compress_Checks
           (Path  : Path_Vertices;
            Var   : Flow_Id;
            Parts : in out Flow_Id_Sets.Set)
         is
            Components : Flow_Id_Sets.Set := Get_Components (Var, FA.B_Scope);
         begin
            --  Get_Components returns Var'Extension_Part if Var is classwide
            --  but not if it is a tagged parameter of a subprogram annotated
            --  with Extensions_Visible. In this case, we need to include
            --  Var'Extension_Part in the components of Var because we want to
            --  compress checks on extension parts as we do it for regular
            --  components.

            if Is_Entire_Variable (Var)
              and then Var.Kind = Direct_Mapping
              and then Var.Variant = Normal_Use
              and then Extensions_Visible (Var, FA.B_Scope)
            then
               Components.Include ((Var with delta Facet => Extension_Part));
            end if;

            --  If Kind_Checks contains Var, Var is a leaf of the tree
            --  representing the type of its entire variable. Else, we recurse
            --  on the components of Var.

            if Kind_Checks (Path).Contains (Var) then
               Parts.Insert (Var);
            else
               --  The sets corresponding to Path in Kind_Checks and
               --  Non_Kind_Checks are disjoint. This means that if a part is
               --  in Non_Kind_Checks, then we won't be able to compress the
               --  checks related to its subcomponents in Kind_Checks.

               declare
                  Path_Position : constant Path_To_Variables_Maps.Cursor :=
                    Non_Kind_Checks.Find (Path);
               begin
                  if not Path_To_Variables_Maps.Has_Element (Path_Position)
                    or else
                      not Non_Kind_Checks (Path_Position).Contains (Var)
                  then
                     --  Var is excluded from Components to avoid infinite
                     --  recursion.

                     Components.Exclude (Var);

                     --  Recursively populate Parts with all the uninitialized
                     --  subcomponents of Var, by recursing on the (possibly
                     --  empty) set of components of Var.

                     for C of Components loop
                        Compress_Checks
                          (Path  => Path,
                           Var   => C,
                           Parts => Parts);
                     end loop;

                     --  If Var doesn't have any components, then, since Path
                     --  isn't mapped to Var in either of the maps, it is not
                     --  uninitialized at V_Use. Else, if Parts contains all
                     --  the components of Var, then we can emit the check on
                     --  Var only. Otherwise, we need to emit checks on all the
                     --  uninitialized subcomponents.

                     if not Components.Is_Empty
                       and then Components.Is_Subset (Parts)
                     then
                        Parts.Difference (Components);
                        Parts.Insert (Var);
                     end if;
                  end if;
               end;
            end if;
         end Compress_Checks;

      --  Start of processing for Emit_Check_Messages

      begin
         for P in Kind_Checks.Iterate loop
            declare
               Path : Path_Vertices renames Path_To_Variables_Maps.Key (P);
               Variables : Flow_Id_Sets.Set renames Kind_Checks (Path);
            begin
               for Var of To_Entire_Variables (Variables) loop
                  declare
                     Parts : Flow_Id_Sets.Set;
                     --  Parts of Var on which we need to emit checks for
                     --  uninitialization.
                  begin
                     Compress_Checks
                       (Path  => Path,
                        Var   => Var,
                        Parts => Parts);

                     --  Emit checks on every uninitialized part of Var

                     for S of Parts loop
                        Emit_Check_Message
                          (Var   => S,
                           Start => Path.Start,
                           V_Use => Path.V_Use,
                           Kind  => Kind);

                        --  Path is mapped to the parts on which we need
                        --  to emit Kind checks to avoid exploring their
                        --  subcomponents again when emitting checks of
                        --  another kind.

                        Variables.Include (S);
                     end loop;
                  end;
               end loop;
            end;
         end loop;
      end Emit_Check_Messages;

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
               Msg      => Proved_Msg (Var),
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
               and then Present (Expression (Declaration_Node (E))))

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
               Msg      => Proved_Msg (Var),
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

      ---------------------
      -- Is_Main_Global_Input --
      ---------------------

      function Is_Main_Global_Input (Atr : V_Attributes) return Boolean is
        (FA.Kind in Kind_Subprogram | Kind_Task
         and then FA.Is_Main
         and then Atr.Is_Global
         and then Atr.Mode in Initialized_Global_Modes);

      --------------------
      -- Is_Initialized --
      --------------------

      function Is_Initialized (F : Flow_Id; Atr : V_Attributes) return Boolean
      is
         (if Is_Main_Global_Input (Atr)
          then Is_Initialized_At_Elaboration (F, FA.B_Scope)
          else Atr.Is_Initialized);

      ----------
      -- Hash --
      ----------

      function Hash (Path : Path_Vertices) return Ada.Containers.Hash_Type
      is
         use type Ada.Containers.Hash_Type;
         use Flow_Graphs;
      begin
         return 17 * Vertex_Hash (Path.Start) + 13 * Vertex_Hash (Path.V_Use);
      end Hash;

      --------------------------------
      -- Has_Relaxed_Initialization --
      --------------------------------

      function Has_Relaxed_Initialization (F : Flow_Id) return Boolean is
      begin
         case F.Kind is
            when Direct_Mapping =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
               begin
                  case Ekind (E) is

                     --  Abstract state can't be annotated

                     when E_Abstract_State =>
                        return False;

                     --  Other objects can be either annotated directly, or
                     --  else the aspect can apply to their type, or else
                     --  the type can be composite with types of all of its
                     --  (sub)components annotated. This is detected and
                     --  stored in marking.

                     when E_Function
                        | E_Variable
                        | E_Constant
                        | Formal_Kind
                     =>
                        return
                          Entity_In_SPARK (E)
                            and then
                          (if Ekind (E) = E_Function
                           then Fun_Has_Relaxed_Init (E)
                           else Obj_Has_Relaxed_Init (E));

                     when others =>
                        return False;
                  end case;
               end;

            when Record_Field =>

               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
               begin
                  --  Record components like "X.Y.Z" can have aspect on the
                  --  object (here "X"), or else on the type of the object, or
                  --  else on the type of its components (here "Y" and "Z"). or
                  --  else, the type can be composite with types of all of its
                  --  (sub)components annotated. Here, we need to explore the
                  --  record fields because the components are not objects, and
                  --  only their type can be annotated with
                  --  Relaxed_Initialization.

                  if Ekind (E) in E_Function
                                | E_Variable
                                | E_Constant
                                | Formal_Kind
                  then
                     return
                       Entity_In_SPARK (E)
                         and then
                       ((if Ekind (E) = E_Function
                         then Fun_Has_Relaxed_Init (E)
                         else Obj_Has_Relaxed_Init (E))
                           or else
                       (for some Comp of F.Component =>
                          (Has_Relaxed_Init (Get_Type (Comp, FA.B_Scope)))));

                  else
                     return False;
                  end if;
               end;

            --  Objects not visible by Entity_Id are assumed to have no
            --  Relaxed_Initialization.

            when Magic_String =>
               return False;

            when others =>
               raise Program_Error;
         end case;
      end Has_Relaxed_Initialization;

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
         --  Global inputs of main-like subprograms that do not appear in the
         --  Initializes contract might still be initialized at elaboration
         --  (e.g. if are only initialized when some condition is satisfied).

         if Is_Main_Global_Input (FA.Atr (V_Initial)) then
            return True;
         end if;

         for V_Def of
           FA.DDG.Get_Collection (V_Use, Flow_Graphs.In_Neighbours)
         loop
            declare
               Def_Atr : V_Attributes renames FA.Atr (V_Def);

            begin
               if V_Def = V_Initial then
                  --  We're using the initial value
                  pragma Assert
                    (Def_Atr.Is_Param_Havoc
                       or else
                     not Is_Initialized
                       (Change_Variant (Var, Initial_Value), Def_Atr));
                  Is_Uninitialized := True;

               elsif V_Def = V_Use then
                  --  This is a self-assignment
                  null;

               elsif Def_Atr.Variables_Defined.Contains (Var)
                 or else Def_Atr.Volatiles_Read.Contains (Var)
               then
                  return True;
               end if;
            end;
         end loop;

         pragma Assert (Is_Uninitialized);

         return False;
      end Might_Be_Initialized;

      ----------------
      -- Proved_Msg --
      ----------------

      function Proved_Msg (Var : Flow_Id) return String is
      begin
         --  Tune message for entire objects whose components are subject to
         --  Relaxed_Initialization.

         if Var.Kind = Direct_Mapping then
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (Var);
            begin
               if Ekind (E) /= E_Abstract_State
                 and then Entity_In_SPARK (E)
                 and then
                   Contains_Relaxed_Init_Parts (Get_Type (E, FA.B_Scope))
               then
                  return "initialization of parts of & " &
                    "without Relaxed_Initialization proved";
               end if;
            end;
         end if;

         return "initialization of & proved";
      end Proved_Msg;

      -------------------
      -- Scan_Children --
      -------------------

      procedure Scan_Children
        (Var                  : Flow_Id;
         V_Initial            : Flow_Graphs.Vertex_Id;
         Possibly_Initialized : Boolean;
         Visited              : in out Vertex_Sets.Set;
         OK                   : in out Boolean)
      is
         procedure Update
           (Checks : in out Path_To_Variables_Maps.Map;
            Start  : Flow_Graphs.Vertex_Id;
            V_Use  : Flow_Graphs.Vertex_Id;
            Var    : Flow_Id);
         --  Maps Start and V_Use to Var in Checks

         ------------
         -- Update --
         ------------

         procedure Update
           (Checks : in out Path_To_Variables_Maps.Map;
            Start  : Flow_Graphs.Vertex_Id;
            V_Use  : Flow_Graphs.Vertex_Id;
            Var    : Flow_Id)
         is
            Path     : constant Path_Vertices := (Start, V_Use);
            Position : Path_To_Variables_Maps.Cursor;
            Unused   : Boolean;
         begin
            Checks.Insert (Path, Position, Unused);
            Checks (Position).Insert (Var);
         end Update;

         Position : Vertex_Sets.Cursor;
         Inserted : Boolean;
         Kind     : Msg_Kind;
         Start    : constant Flow_Graphs.Vertex_Id :=
           (if FA.Atr (V_Initial).Is_Param_Havoc
            then V_Initial
            else FA.Start_Vertex);
         --  When emitting a check message, if we scan children of a havoc
         --  vertex, then we will search from the havoc vertex itself;
         --  otherwise, we will skip the 'Initial vertex and begin from the
         --  start of the subprogram.

      begin
         for Child of
           FA.PDG.Get_Collection (V_Initial, Flow_Graphs.Out_Neighbours)
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
                        OK   := False;
                        Kind := (if Possibly_Initialized
                                   or else
                                    Might_Be_Initialized
                                      (Var       => Var,
                                       V_Initial => V_Initial,
                                       V_Use     => Child)
                                 then Unknown
                                 else Err);

                        if Kind = Err then
                           Update
                             (Checks => Err_Checks,
                              Start  => Start,
                              V_Use  => Child,
                              Var    => Var);
                        else
                           Update
                             (Checks => Unknown_Checks,
                              Start  => Start,
                              V_Use  => Child,
                              Var    => Var);
                        end if;

                     --  Otherwise, it is a partial assignment, e.g.
                     --     Arr (X) := Y;
                     --  which is modellled as:
                     --     Arr := (X => Y, others => Arr ("others"));
                     --  and we keep looking for genuine reads of the array.

                     else
                        Scan_Children
                          (Var,
                           V_Initial            => Child,
                           Possibly_Initialized => True,
                           Visited              => Visited,
                           OK                   => OK);
                     end if;

                  else
                     if Child_Atr.Variables_Used.Contains (Var) then
                        OK   := False;
                        Kind := (if Might_Be_Initialized
                                      (Var       => Var,
                                       V_Initial => V_Initial,
                                       V_Use     => Child)
                                 then Unknown
                                 else Err);

                        if Kind = Err then
                           Update
                             (Checks => Err_Checks,
                              Start  => Start,
                              V_Use  => Child,
                              Var    => Var);
                        else
                           Update
                             (Checks => Unknown_Checks,
                              Start  => Start,
                              V_Use  => Child,
                              Var    => Var);
                        end if;
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
      --  each component on each location where it is accessed without being
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

            OK : Boolean := True;
            --  This flag will be initially True, but will become False if
            --  any check is emitted when scanning the flow graph. If no such
            --  checks are emitted, then all uses of the considered object are
            --  safe and we will get a single info message.

         begin
            if Parent_Key.Variant = Initial_Value
              and then not Synthetic (Parent_Key)
              and then not Is_Empty_Record_Object (Parent_Key)
              and then not Has_Relaxed_Initialization (Parent_Key)
              and then not Is_Initialized (Parent_Key, Parent_Atr)
            then
               Scan_Children
                 (Var                  => Change_Variant
                                            (Parent_Key, Normal_Use),
                  V_Initial            => Parent,
                  Possibly_Initialized => False,
                  Visited              => Visited,
                  OK                   => OK);

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

            --  Do the same for variables that become havoced after a call that
            --  raised an exception.

            elsif Parent_Atr.Is_Param_Havoc then
               for Havoc_Var of Parent_Atr.Variables_Defined loop
                  Scan_Children
                    (Var                  => Havoc_Var,
                     V_Initial            => Parent,
                     Possibly_Initialized => False,
                     Visited              => Visited,
                     OK                   => OK);

                  declare
                     Havoc_Atr : V_Attributes renames
                       FA.Atr (Get_Initial_Vertex (FA.DDG, Havoc_Var));
                     --  Attributes of the initial vertex of the havoced
                     --  variable.

                     Obj : constant Flow_Id := Entire_Variable (Havoc_Var);
                  begin
                     if Havoc_Atr.Is_Global then
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
               end loop;
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

              --  Ignore own objects of the analysed package, but only for
              --  packages with a generated Initializes contract.

              or else (Parent_Key.Variant = Final_Value
                       and then Parent_Atr.Is_Export
                       and then Ekind (FA.Spec_Entity) = E_Package
                       and then No (FA.Initializes_N))

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

      Emit_Check_Messages
        (Kind            => Err,
         Kind_Checks     => Err_Checks,
         Non_Kind_Checks => Unknown_Checks);
      Emit_Check_Messages
        (Kind            => Unknown,
         Kind_Checks     => Unknown_Checks,
         Non_Kind_Checks => Err_Checks);

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

   ----------------------------
   -- Find_Stable_Conditions --
   ----------------------------

   procedure Find_Stable_Conditions (FA : in out Flow_Analysis_Graphs) is

      function Is_While_Loop (N : N_Loop_Statement_Id) return Boolean is
        (Present (Condition (Iteration_Scheme (N))));
      --  Returns True if F is a WHILE loop

      function Is_Stable (Loop_Id        : E_Loop_Id;
                          Condition_Vars : Flow_Id_Sets.Set) return Boolean
        with Pre => not Condition_Vars.Is_Empty;
      --  True if none of the Condition_Vars is written inside the Loop_Id body

      procedure Error_Msg (Msg : String; N : Node_Id);
      --  Output an error message attached to the loop identifier

      ---------------
      -- Is_Stable --
      ---------------

      function Is_Stable (Loop_Id        : E_Loop_Id;
                          Condition_Vars : Flow_Id_Sets.Set) return Boolean is
      begin
         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);
            begin
               if Atr.Loops.Contains (Loop_Id)
                 and then (for some Var_Def of Atr.Variables_Defined =>
                             Condition_Vars.Contains (Var_Def))
               then
                  return False;
               end if;
            end;
         end loop;

         return True;
      end Is_Stable;

      ---------------
      -- Error_Msg --
      ---------------

      procedure Error_Msg (Msg : String; N : Node_Id) is
      begin
         Error_Msg_Flow
           (FA       => FA,
            Msg      => Msg,
            N        => N,
            Tag      => Stable,
            Severity => Warning_Kind);
      end Error_Msg;

   --  Start of processing for Find_Stable_Conditions

   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Cond_Id  : constant Flow_Id := FA.CFG.Get_Key (V);
            Cond_Atr : V_Attributes renames FA.Atr (V);

         begin
            if not Cond_Atr.Variables_Used.Is_Empty
              and then Cond_Id.Kind = Direct_Mapping
            then
               case Nkind (Cond_Id.Node) is
                  --  If none of the variables used in the loop condition are
                  --  modified in the loop body, then the loop is considered
                  --  stable.
                  when N_Loop_Statement =>
                     if Is_While_Loop (Cond_Id.Node)
                       and then
                         Is_Stable (Loop_Id        =>
                                      Entity (Identifier (Cond_Id.Node)),
                                    Condition_Vars => Cond_Atr.Variables_Used)
                     then
                        Error_Msg (Msg => "loop condition is stable",
                                   N   => Cond_Id.Node);
                     end if;
                  when N_Exit_Statement =>
                     if Is_Stable (Loop_Id        =>
                                     Loop_Entity_Of_Exit_Statement
                                       (Cond_Id.Node),
                                   Condition_Vars => Cond_Atr.Variables_Used)
                     then
                        Error_Msg (Msg => "loop exit condition is stable",
                                   N   => Cond_Id.Node);
                     end if;
                  when others =>
                     null;
               end case;
            end if;
         end;
      end loop;
   end Find_Stable_Conditions;

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
        and then Has_User_Supplied_Globals (FA.Spec_Entity)
      then
         Raw_Globals := Contract_Globals (FA.Spec_Entity);

         Only_Global_Inputs := Raw_Globals.Inputs - Raw_Globals.Outputs;

         for Input of Only_Used_In_Assertions (Only_Global_Inputs) loop
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& must be a Proof_In as it is only " &
                           "used in assertions",
               SRM_Ref  => "6.1.4(19)",
               N        => Find_Global (FA.Spec_Entity,
                                        Direct_Mapping_Id (Input)),
               F1       => Direct_Mapping_Id (Input),
               Tag      => Global_Wrong,
               Severity => Medium_Check_Kind);
         end loop;
      end if;
   end Find_Input_Only_Used_In_Assertions;

   -------------------------------------
   -- Find_Illegal_Reads_Of_Proof_Ins --
   -------------------------------------

   procedure Find_Illegal_Reads_Of_Proof_Ins
     (FA : in out Flow_Analysis_Graphs)
   is
      use Flow_Graphs;

      Globals : Global_Flow_Ids;

   begin
      --  We start from a user-written contract, scan each of its Proof_In
      --  global, each of its flattened component and each of its use. This
      --  is more efficient than scanning the entire CFG.

      if FA.Kind in Kind_Subprogram | Kind_Task
        and then Has_User_Supplied_Globals (FA.Spec_Entity)
      then
         Get_Globals (Subprogram          => FA.Spec_Entity,
                      Scope               => FA.B_Scope,
                      Classwide           => False,
                      Globals             => Globals,
                      Use_Deduced_Globals => False,
                      Ignore_Depends      => True);

         for Proof_In of Globals.Proof_Ins loop
            for Var of Flatten_Variable (Proof_In, FA.B_Scope) loop
               declare
                  Initial_V : constant Flow_Graphs.Vertex_Id :=
                    Get_Initial_Vertex (FA.CFG,
                                        Change_Variant (Var, Normal_Use));

                  pragma Assert (FA.Atr (Initial_V).Is_Global);
                  pragma Assert (FA.Atr (Initial_V).Mode = Mode_Proof);

               begin
                  for Use_V of
                    FA.PDG.Get_Collection (Initial_V, Out_Neighbours)
                  loop
                     declare
                        Use_F : Flow_Id      renames FA.PDG.Get_Key (Use_V);
                        Use_A : V_Attributes renames FA.Atr (Use_V);

                     begin
                        --  Ignore final uses

                        if Use_F.Variant = Final_Value then
                           null;

                        --  Ignore uses in assertion expressions

                        elsif Use_A.Is_Assertion then
                           null;

                        --  Ignore vertices generated by "null => ..."
                        --  Initializes clauses.

                        elsif Use_A.Is_Package_Initialization
                          and then Use_A.Variables_Defined.Is_Empty
                        then
                           null;

                        else
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "Proof_In global & " &
                                          "can only be used in assertions",
                              SRM_Ref  => "6.1.4(19)",
                              N        => First_Variable_Use
                                (N       => Use_A.Error_Location,
                                 Scope   => FA.B_Scope,
                                 Var     => Var,
                                 Precise => False),
                              F1       => Var,
                              Vertex   => Use_V,
                              Tag      => Global_Wrong,
                              Severity => Medium_Check_Kind);
                        end if;
                     end;
                  end loop;
               end;
            end loop;
         end loop;
      end if;
   end Find_Illegal_Reads_Of_Proof_Ins;

   -----------------------------------------
   -- Find_Impossible_To_Initialize_State --
   -----------------------------------------

   procedure Find_Impossible_To_Initialize_State
     (FA : in out Flow_Analysis_Graphs)
   is
      DM : constant Dependency_Maps.Map :=
        Parse_Initializes (FA.Spec_Entity, FA.S_Scope);

      Subprogram_Outputs : Flow_Id_Sets.Set;
      --  Abstracts states that are written by subprograms declared in package
      --  specification.

      function Initialized_By_Initializes (F : Flow_Id) return Boolean
      with Pre => Is_Abstract_State (F);
      --  Returns True iff F is initialized by the Initializess aspect (either
      --  generated or provided by the user).

      procedure Collect_Subprogram_Outputs
      with Global => (Output => Subprogram_Outputs);
      --  Populate Subprogram_Outputs

      function Trivially_Initialized (E : Entity_Id) return Boolean
      with Pre => Ekind (E) = E_Abstract_State;
      --  Returns True iff declaration of E says it is initialized

      --------------------------------
      -- Initialized_By_Initializes --
      --------------------------------

      function Initialized_By_Initializes (F : Flow_Id) return Boolean
        renames DM.Contains;

      --------------------------------
      -- Collect_Subprogram_Outputs --
      --------------------------------

      procedure Collect_Subprogram_Outputs is
         E : Entity_Id;
      begin
         E := First_Entity (FA.Spec_Entity);
         while Present (E) loop
            if Ekind (E) = E_Procedure
              or else (Ekind (E) = E_Function
                       and then Is_Function_With_Side_Effects (E))
            then
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
                        Subprogram_Outputs.Include
                          (Change_Variant (Write, Normal_Use));
                     end if;
                  end loop;
               end;
            end if;

            Next_Entity (E);
         end loop;
      end Collect_Subprogram_Outputs;

      function Trivially_Initialized (E : Entity_Id) return Boolean is
        (Has_Volatile (E)
         and then Has_Volatile_Property (E, Pragma_Async_Writers));

   --  Start of processing for Find_Impossible_To_Initialize_State

   begin
      if Has_Non_Null_Abstract_State (FA.Spec_Entity) then
         Collect_Subprogram_Outputs;

         --  Issue error for every non-null abstract state that does not have
         --  Async_Writers, is not mentioned in an Initializes aspect and is
         --  not a pure output of an externally visible procedure.

         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            if not Trivially_Initialized (State)
                and then
              not Initialized_By_Initializes (Direct_Mapping_Id (State))
                and then
              not Subprogram_Outputs.Contains (Direct_Mapping_Id (State))
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "no subprogram exists that can initialize " &
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
        (Deps    : Dependency_Maps.Map;
         Globals : Global_Flow_Ids)
         return Dependency_Maps.Map;
      --  Strips global Proof_Ins from the RHS of Deps

      procedure Prepare_Trimming
        (Globals :     Global_Flow_Ids;
         Inputs  : out Flow_Id_Sets.Set;
         Outputs : out Flow_Id_Sets.Set);
      --  Prepare sets with inputs and outputs for trimming an explicit Depends
      --  using Refined_Global.
      --  ??? this code duplicates the trimming that happens in Get_Depends

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

      ----------------------
      -- Prepare_Trimming --
      ----------------------

      procedure Prepare_Trimming
        (Globals :     Global_Flow_Ids;
         Inputs  : out Flow_Id_Sets.Set;
         Outputs : out Flow_Id_Sets.Set)
      is
      begin
         --  Change all variants to Normal_Use

         Inputs  := Change_Variant (Globals.Inputs,  Normal_Use);
         Outputs := Change_Variant (Globals.Outputs, Normal_Use);

         --  Add formal parameters

         for Param of Get_Formals (FA.Spec_Entity) loop
            declare
               Formal_Param : constant Flow_Id := Direct_Mapping_Id (Param);

            begin
               case Ekind (Param) is
               when E_In_Parameter =>
                  Inputs.Insert (Formal_Param);
                  if Is_Access_Type (Underlying_Type (Etype (Param))) then
                     --  ??? this should be added to Get_Depends
                     Outputs.Insert (Formal_Param);
                  end if;

               when E_In_Out_Parameter =>
                  Inputs.Insert (Formal_Param);
                  Outputs.Insert (Formal_Param);

               when E_Out_Parameter =>
                  Outputs.Insert (Formal_Param);

               when E_Protected_Type | E_Task_Type =>
                  Inputs.Insert (Formal_Param);
                  if Ekind (FA.Spec_Entity) /= E_Function then
                     Outputs.Insert (Formal_Param);
                  end if;

               when others =>
                  raise Program_Error;
               end case;
            end;
         end loop;

         --  If we analyze a function then we need to add it to the outputs so
         --  that Function'Result can appear on the LHS of the Depends.

         if Ekind (FA.Spec_Entity) = E_Function then
            Outputs.Insert (Direct_Mapping_Id (FA.Spec_Entity));
         end if;

      end Prepare_Trimming;

      ---------------------
      -- Strip_Proof_Ins --
      ---------------------

      function Strip_Proof_Ins
        (Deps    : Dependency_Maps.Map;
         Globals : Global_Flow_Ids)
         return Dependency_Maps.Map
      is
         --  Global Proof_Ins cannot appear in the RHS of a Depends contract.
         --  We get them here because Compute_Dependency_Relation returns them
         --  and this is used in Find_Exports_Derived_From_Proof_Ins.

         Stripped : Dependency_Maps.Map;

      begin
         for C in Deps.Iterate loop
            declare
               G_Out : Flow_Id          renames Dependency_Maps.Key (C);
               G_Ins : Flow_Id_Sets.Set renames FA.Dependency_Map (C);

               Ins : Flow_Id_Sets.Set;

            begin
               for G_In of G_Ins loop
                  if Globals.Proof_Ins.Contains
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

      Missing_Deps : Dependency_Maps.Map;
      Unused_Deps  : Dependency_Maps.Map;

      Globals : Global_Flow_Ids;
      Inputs  : Flow_Id_Sets.Set;
      Outputs : Flow_Id_Sets.Set;
      --  Inputs and outputs that appear on the PDG

      Depends_Scope : constant Flow_Scope := (if Present (FA.Refined_Depends_N)
                                              then FA.B_Scope
                                              else FA.S_Scope);
      --  This is body scope if we are checking a Refined_Depends contract or
      --  spec scope if we are checking a Depends contract.

      Contract_N : constant Node_Id :=
        (if Present (FA.Refined_Depends_N)
         then FA.Refined_Depends_N
         else FA.Depends_N);

   --  Start of processing for Check_Depends_Contract

   begin
      --  If the user has not specified a dependency relation we have no work
      --  to do.

      if No (Contract_N) then
         return;
      end if;

      Get_Globals (FA.Spec_Entity, FA.B_Scope, False, Globals);

      --  Read the user-written Depends

      User_Deps := (if Present (FA.Refined_Depends_N)
                    then Parse_Depends (FA.Refined_Depends_N)
                    else Parse_Depends (FA.Depends_N));

      --  Read the generated Refined_Depends

      Actual_Deps := Strip_Proof_Ins (FA.Dependency_Map, Globals);

      --  Up-project the dependencies

      Up_Project (User_Deps,   Projected_User_Deps, Depends_Scope);
      Up_Project (Actual_Deps, Projected_Actual_Deps, Depends_Scope);

      --  Detect inconsistent dependencies

      Check (Generated => Projected_Actual_Deps,
             User      => Projected_User_Deps,
             Missing   => Missing_Deps,
             Unused    => Unused_Deps);

      --  Prepare inputs and outputs for trimming

      Prepare_Trimming (Globals, Inputs, Outputs);

      --  Debug output

      pragma Annotate (Xcov, Exempt_On, "Debugging code");
      if Debug_Trace_Depends then
         Write_Line (Get_Name_String (Chars (FA.Spec_Entity)) & ":");
         Print_Dependency_Map ("user",    Projected_User_Deps);
         Print_Dependency_Map ("actual",  Actual_Deps);
         Print_Dependency_Map ("missing", Missing_Deps);
         Print_Dependency_Map ("unused",  Unused_Deps);
      end if;
      pragma Annotate (Xcov, Exempt_Off);

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
                                 (FA.Spec_Entity,
                                  Get_Direct_Mapping_Id (Unused_Out)),
                  F1       => Unused_Out,
                  F2       => Direct_Mapping_Id (FA.Spec_Entity),
                  Tag      => Depends_Null,
                  Severity => Medium_Check_Kind);
            end if;

            for Unused_In of Unused_Ins loop

               --  If the RHS mentions an extra state with visible null
               --  refinement then we suppress the check as trivially void.

               if Is_Dummy_Abstract_State (Unused_In, FA.B_Scope) then
                  null;

               --  Extra items on the RHS of a user dependency

               elsif not Is_Variable (Unused_In) then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& cannot appear in Depends",
                     N        => Search_Depends_Contract
                                   (FA.Spec_Entity,
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
                                   (FA.Spec_Entity,
                                    Empty,
                                    Get_Direct_Mapping_Id (Unused_In)),
                     F1       => Unused_In,
                     Tag      => Depends_Wrong,
                     Severity => Medium_Check_Kind);

               elsif Unused_Out = Direct_Mapping_Id (FA.Spec_Entity)
                 and then Ekind (FA.Spec_Entity) = E_Function
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "incorrect dependency ""%'Result => %""",
                     N        => Search_Depends_Contract
                                   (FA.Spec_Entity,
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
                                   (FA.Spec_Entity,
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
               if Missing_Out = Null_Flow_Id then
                  null;

               else
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "expected to see & on the left-hand-side of" &
                                 " a dependency relation",
                     N        => Contract_N,
                     F1       => Missing_Out,
                     Tag      => Depends_Missing_Clause,
                     Severity => Medium_Check_Kind);
               end if;
            end if;

            for Missing_In of Missing_Ins loop

               --  Items missing from the RHS of a user dependency
               if Missing_Out = Null_Flow_Id then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "missing dependency ""null => %""",
                     N        => Search_Depends_Contract
                                   (FA.Spec_Entity, Output => Empty),
                     F1       => Missing_In,
                     Tag      => Depends_Null,
                     Severity => Medium_Check_Kind);
               else
                  declare
                     use Flow_Id_Sets;

                     Path : constant Vertex_Sets.Set :=
                       Dependency_Path
                         (FA      => FA,
                          Inputs  =>
                            Down_Project (Missing_In,  FA.B_Scope)
                              and Inputs,
                          Outputs => Down_Project (Missing_Out, FA.B_Scope)
                              and Outputs);

                  begin
                     if Missing_Out = Direct_Mapping_Id (FA.Spec_Entity) then
                        Error_Msg_Flow
                          (FA       => FA,
                           Path     => Path,
                           Msg      => "missing dependency ""%'Result => " &
                             "%""",
                           N        => Search_Depends_Contract
                             (FA.Spec_Entity,
                              FA.Spec_Entity),
                           F1       => Missing_Out,
                           F2       => Missing_In,
                           Tag      => Depends_Missing,
                           Severity => Medium_Check_Kind);

                     else
                        declare
                           N : constant Node_Id :=
                             Search_Depends_Contract
                               (FA.Spec_Entity,
                                Get_Direct_Mapping_Id (Missing_Out));

                           Kind : constant String :=
                             (if Missing_Out = Missing_In
                              then "self-dependency "
                              else "dependency ");

                           function Hint (F : Flow_Id) return String;
                           --  Return a hint about F being a self-dependency on
                           --  implicit input.

                           ----------
                           -- Hint --
                           ----------

                           function Hint (F : Flow_Id) return String is
                              Typ : Entity_Id;
                           begin
                              if not Is_Abstract_State (F)
                                and then F.Kind = Direct_Mapping
                              then
                                 Typ := Get_Type (F, FA.B_Scope);
                              else
                                 return "";
                              end if;

                              if Is_Tagged_Type (Typ) then
                                 return " (tag is preserved)";

                              elsif Is_Array_Type (Typ)
                                and then not Is_Constrained (Typ)
                              then
                                 return " (array bounds are preserved)";

                              elsif Is_Record_Type (Typ)
                                and then not Is_Constrained (Typ)
                              then
                                 return " (discriminants are preserved)";

                              else
                                 return "";
                              end if;
                           end Hint;

                        begin
                           Error_Msg_Flow
                             (FA       => FA,
                              Path     => Path,
                              Msg      => "missing " & Kind & """% => %""" &
                                (if Missing_Out = Missing_In
                                 then Hint (Missing_Out) else ""),
                              N        => N,
                              F1       => Missing_Out,
                              F2       => Missing_In,
                              Tag      => Depends_Missing,
                              Severity => Medium_Check_Kind);
                        end;
                     end if;
                  end;
               end if;
            end loop;
         end;
      end loop;
   end Check_Depends_Contract;

   ------------------------------------
   -- Check_Ghost_Subprogram_Outputs --
   ------------------------------------

   procedure Check_Ghost_Subprogram_Outputs (FA : in out Flow_Analysis_Graphs)
   is
      Globals : Global_Flow_Ids;
   begin
      if (Ekind (FA.Spec_Entity) = E_Procedure
            or else Is_Function_With_Side_Effects (FA.Spec_Entity))
        and then Is_Ghost_Entity (FA.Spec_Entity)
      then
         Get_Globals (Subprogram => FA.Spec_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         for Output of Globals.Outputs loop
            if not Is_Ghost_Entity (Output) then
               Error_Msg_Flow (FA       => FA,
                               Msg      => "ghost subprogram & cannot have " &
                                           "non-ghost global output &",
                               N        => FA.Spec_Entity,
                               F1       => Direct_Mapping_Id
                                             (FA.Spec_Entity),
                               F2       => Output,
                               Severity => Medium_Check_Kind,
                               Tag      => Ghost_Wrong,
                               SRM_Ref  => "6.9(20)");
            end if;
         end loop;
      end if;
   end Check_Ghost_Subprogram_Outputs;

   ------------------------
   -- Check_Hidden_State --
   ------------------------

   procedure Check_Hidden_State (FA : in out Flow_Analysis_Graphs) is

      procedure Examine_Own_Variable
        (E       : Entity_Id;
         Owner   : Entity_Id;
         Visible : Boolean)
      with Pre => Ekind (E) in E_Abstract_State | E_Constant | E_Variable
                    and then Ekind (Owner) = E_Package;
      --  Examine whether state variable E is legally belonging to Owner

      procedure Examine_Declarations (L : List_Id; Visible : Boolean);
      --  Examine objects from the declaration L, which are either visible
      --  to outside of the current package or hidden in its private and
      --  body parts.

      --------------------------
      -- Examine_Own_Variable --
      --------------------------

      procedure Examine_Own_Variable
        (E       : Entity_Id;
         Owner   : Entity_Id;
         Visible : Boolean)
      is
         procedure Check_Enclosing_Package;
         --  Check if E is a legal state variable of the enclosing package of
         --  the Owner.

         procedure Illegal_Constituent;
         --  Complain about a state variable that should be a consituent

         function Is_Private_State (Item : Entity_Id) return Boolean
         with Pre => Ekind (Item) in E_Constant | E_Package;
         --  Returns True if Item appears in the private part of the Owner

         -----------------------------
         -- Check_Enclosing_Package --
         -----------------------------

         procedure Check_Enclosing_Package is
            Enclosing_Pkg : constant Entity_Id := Scope (Owner);

         begin
            if Ekind (Enclosing_Pkg) /= E_Package then
               return;

            elsif Enclosing_Pkg = Standard_Standard then
               return;
            end if;

            Examine_Own_Variable
              (E, Enclosing_Pkg,
               Visible =>
                 (if Is_Child_Unit (Owner)
                  then
                    not Is_Private_Descendant (Owner)
                  else
                    List_Containing (Package_Spec (Owner)) =
                      Visible_Declarations
                        (Package_Specification (Enclosing_Pkg))));
         end Check_Enclosing_Package;

         -------------------------
         -- Illegal_Constituent --
         -------------------------

         procedure Illegal_Constituent is
         begin
            --  If possible, we prefer to complain specifically about a missing
            --  Part_Of. Frontend does this reliably for abstract states and
            --  variables, so we only need to worry about constants.

            if Ekind (E) = E_Constant and then Is_Private_State (E) then
               declare
                  Context : constant Entity_Id := Scope (E);
                  Msg     : constant String :=
                    (if Is_Child_Unit (Context)
                     then "visible part of the private child"
                     else "private part of package");
                  SRM_Ref : constant String :=
                    (if Is_Child_Unit (Context)
                     then "7.2.6(3)"
                     else "7.2.6(2)");
               begin
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "indicator Part_Of is required in this " &
                                 "context: & is declared in the " & Msg & " &",
                     SRM_Ref  => SRM_Ref,
                     N        => E,
                     Severity => Error_Kind,
                     F1       => Direct_Mapping_Id (Unique_Entity (E)),
                     F2       => Direct_Mapping_Id (Owner));
               end;
            else
               --  ??? This is a legality and not a verification rule, so the
               --  violation should be reported as an error and not as a check.

               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "& needs to be a constituent " &
                              "of some state abstraction",
                  N        => E,
                  F1       => Direct_Mapping_Id (E),
                  Tag      => Hidden_Unexposed_State,
                  Severity => Medium_Check_Kind);
            end if;
         end Illegal_Constituent;

         ----------------------
         -- Is_Private_State --
         ----------------------

         function Is_Private_State (Item : Entity_Id) return Boolean is
            Context : constant Entity_Id := Scope (Item);

            Context_Specification : constant Node_Id :=
              Package_Specification (Context);

         begin
            --  We reclimb the scope hierarchy, just like when detecting the
            --  owner of a state variable, but without the implicit conversion
            --  of objects declared in package bodies to singleton abstract
            --  states. This partly repeates the discovery of the Owner, but
            --  it seems easier to have those two climbs separated.

            if Context = Owner then
               return List_Containing (Enclosing_Declaration (Item)) =
                 Private_Declarations (Context_Specification)
                   or else
                (Is_Private_Descendant (Context)
                 and then List_Containing (Enclosing_Declaration (Item)) =
                           Visible_Declarations (Context_Specification));
            else
               if Is_Child_Unit (Item) then
                  pragma Assert (not Is_Private_Descendant (Item));
                  return Is_Private_State (Context);
               else
                  return List_Containing (Enclosing_Declaration (Item)) =
                      Visible_Declarations (Context_Specification)
                    and then Is_Private_State (Context);
               end if;
            end if;
         end Is_Private_State;

      --  Start of processing for Examine_Own_Variable

      begin
         --  Variable is exposed in the visible part of the package spec

         if Visible then

            --  Private child units must have their visible variables
            --  annotated with a Part_Of that is consistent with the
            --  corresponding Refined_State in the parent unit body, if any.

            if Is_Child_Unit (Owner)
              and then Is_Private_Descendant (Owner)
            then
               declare
                  Parent_State : constant Entity_Id := Encapsulating_State (E);
               begin
                  if Present (Parent_State) then
                     if Refinement_Exists (Parent_State)
                       and then not Find_In_Refinement (Parent_State, E)
                     then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "refinement of % shall mention %",
                           Severity => Error_Kind,
                           F1       => Direct_Mapping_Id (Parent_State),
                           F2       => Direct_Mapping_Id (E),
                           N        => Scope (Parent_State),
                           SRM_Ref  => "7.2.6(6)");
                     end if;
                  else
                     Illegal_Constituent;
                  end if;
               end;
            else
               Check_Enclosing_Package;
            end if;

         --  Otherwise the variable is hidden, either in the private part of
         --  package spec or in the package body.

         else
            --  If the owner package explicitly declares an abstract state,
            --  then the hidden variable must be explicitly a constituent.

            if Present (Get_Pragma (Owner, Pragma_Abstract_State))
              and then No (Encapsulating_State (E))
            then
               Illegal_Constituent;

            --  Otherwise, keep checking because either some of the enclosing
            --  packages might have an abstract state or it might be a private
            --  child that requires us to check consistency between Part_Of and
            --  Refined_State contracts.

            else
               Check_Enclosing_Package;
            end if;
         end if;
      end Examine_Own_Variable;

      --------------------------
      -- Examine_Declarations --
      --------------------------

      procedure Examine_Declarations (L : List_Id; Visible : Boolean) is
         N : Node_Id := First (L);
      begin
         while Present (N) loop
            if Nkind (N) = N_Object_Declaration then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
               begin
                  if Is_Internal (E) then
                     null;

                  elsif Ekind (E) = E_Variable
                    or else Is_Access_Variable (Etype (E))
                    or else Has_Variable_Input (E)
                  then
                     Examine_Own_Variable (E, FA.Spec_Entity, Visible);
                  end if;
               end;
            end if;

            Next (N);
         end loop;
      end Examine_Declarations;

      --  Local variables

      Pkg_Spec : constant Node_Id := Package_Specification (FA.Spec_Entity);
      Pkg_Body : constant Node_Id := Package_Body (FA.Spec_Entity);

   --  Start of processing for Check_Hidden_State

   begin
      --  Examine all state declared in the current package, i.e. its abstract
      --  states and objects declared within the visible, private and body
      --  declarations (while respecting the SPARK_Mode => Off boundary).

      if Has_Non_Null_Abstract_State (FA.Spec_Entity) then
         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            Examine_Own_Variable (State, FA.Spec_Entity, Visible => True);
         end loop;
      end if;

      Examine_Declarations (Visible_Declarations (Pkg_Spec), Visible => True);

      if Private_Spec_In_SPARK (FA.Spec_Entity) then
         Examine_Declarations
           (Private_Declarations (Pkg_Spec), Visible => False);

         if Entity_Body_In_SPARK (FA.Spec_Entity) then
            Examine_Declarations (Declarations (Pkg_Body), Visible => False);
         end if;
      end if;
   end Check_Hidden_State;

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

      if Is_Library_Level_Entity (FA.Spec_Entity) then
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
                       Dependency_Path
                         (FA      => FA,
                          Inputs  => Flow_Id_Sets.To_Set (Actual_In),
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

      for Var of States_And_Objects (FA.Spec_Entity) loop
         declare
            LHS            : constant Flow_Id := Direct_Mapping_Id (Var);
            RHS            : Flow_Id_Sets.Set;
            LHS_Components : Flow_Id_Sets.Set;

         begin
            if not DM.Contains (LHS) then
               for Constituent of Down_Project (Var, FA.B_Scope) loop

                  --  ??? It would be better if we wouldn't get things that are
                  --  not in SPARK here but at the moment Down_Project does
                  --  return them. This need to be fixed in Down_Project.

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
                                Inputs  =>
                                  Flow_Id_Sets.To_Set
                                    (Change_Variant (Input, Normal_Use)),
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
                 Get_Pragma (Body_Entity (FA.Spec_Entity),
                             Pragma_Refined_State);

            begin
               for State of Iter (Abstract_States (FA.Spec_Entity)) loop
                  if not Has_Null_Refinement (State) then
                     for Constituent of Iter (Refinement_Constituents (State))
                     loop
                        if Ekind (Constituent) = E_Constant
                          and then not Is_Access_Variable (Etype (Constituent))
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
                    and then not Is_Access_Variable (Etype (Constituent))
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

      Protected_Subp : constant Entity_Id :=
        Subprograms.Enclosing_Subprogram (FA.Spec_Entity);

      Protected_Type : Entity_Id;
      --  For detecting external calls to the same object

   --  Start of processing for Check_Potentially_Blocking

   begin
      if Is_Protected_Operation (Protected_Subp) then
         Protected_Type := Scope (Protected_Subp);
         pragma Assert (Ekind (Protected_Type) = E_Protected_Type);
      else
         return;
      end if;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);

            Blocking_Callee       : Any_Entity_Name;
            Call_With_Same_Target : External_Call;
            --  Will keep a detailed reason for operations that are potentially
            --  blocking due to indirect calls to other subprograms.

         begin
            --  Ignore vertices coming from nested packages

            if Atr.In_Nested_Package then
               null;

            --  Detect delay statements

            elsif Atr.Is_Program_Node
              and then Is_Delay_Statement (FA.CFG.Get_Key (V))
            then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      =>
                    "potentially blocking delay statement " &
                    "in protected operation &",
                  N        => Atr.Error_Location,
                  F1       => Direct_Mapping_Id (Protected_Subp),
                  Tag      => Potentially_Blocking_In_Protected,
                  Severity => High_Check_Kind,
                  Vertex   => V);

            --  Detect violations coming from subprogram calls

            else
               for SC of Atr.Subprogram_Calls loop

                  --  Ignore elaboration of nested packages

                  if Ekind (SC.E) = E_Package then
                     null;

                  --  Calls via access-to-subprogram are not potentially
                  --  blocking, because attribute Access is only allowed on
                  --  subprograms with null globals.

                  elsif Ekind (SC.E) = E_Subprogram_Type then
                     null;

                  --  Calls to entries are trivially potentially blocking

                  elsif Is_Entry (SC.E) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "potentially blocking entry call " &
                          "in protected operation &",
                        N        => Atr.Error_Location,
                        F1       => Direct_Mapping_Id (Protected_Subp),
                        Tag      => Potentially_Blocking_In_Protected,
                        Severity => High_Check_Kind,
                        Vertex   => V);

                  elsif Nkind (SC.N) in N_Subprogram_Call
                    and then Flow_Classwide.Is_Dispatching_Call (SC.N)
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "potentially blocking dispatching call " &
                          "in protected operation &",
                        N        => Atr.Error_Location,
                        F1       => Direct_Mapping_Id (Protected_Subp),
                        Tag      => Potentially_Blocking_In_Protected,
                        Severity => High_Check_Kind,
                        Vertex   => V);

                  --  Predefined potentially blocking routines are identified
                  --  individually, because they are not analyzed in phase 1.

                  elsif Lib.In_Predefined_Unit (SC.E) then
                     if Is_Predefined_Potentially_Blocking (SC.E) then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             "call to potentially blocking " &
                             "predefined subprogram & " &
                             "in protected operation &",
                           N        => Atr.Error_Location,
                           F1       => Direct_Mapping_Id (SC.E),
                           F2       => Direct_Mapping_Id (Protected_Subp),
                           Tag      => Potentially_Blocking_In_Protected,
                           Severity => High_Check_Kind,
                           Vertex   => V);
                     end if;

                  --  Direct calls to potentially blocking subprograms

                  elsif Has_Potentially_Blocking_Statement (SC.E) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      =>
                          "call to potentially blocking subprogram & " &
                          "in protected operation &",
                        N        => Atr.Error_Location,
                        F1       => Direct_Mapping_Id (SC.E),
                        F2       => Direct_Mapping_Id (Protected_Subp),
                        Tag      => Potentially_Blocking_In_Protected,
                        Severity => High_Check_Kind,
                        Vertex   => V);

                  --  ??? For indirect calls we would prefer to emit a detailed
                  --  trace of calls that leads to a potentially blocking
                  --  operation, but this requires storing the slocs of both
                  --  direct calls and potentially blocking operations within
                  --  the ALI file and a copy of the original call graph (and
                  --  not its transitive closure).

                  else

                     --  Indirect calls to potentially blocking subprograms

                     Blocking_Callee := Potentially_Blocking_Callee (SC.E);

                     if Blocking_Callee /= Null_Entity_Name then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      =>
                             "call to potentially blocking subprogram & " &
                             "in protected operation &",
                           N        => Atr.Error_Location,
                           F1       => Magic_String_Id (Blocking_Callee),
                           F2       => Direct_Mapping_Id (Protected_Subp),
                           Tag      => Potentially_Blocking_In_Protected,
                           Severity => High_Check_Kind,
                           Vertex   => V);

                     --  An external call on a protected subprogram with the
                     --  same target object as that of the protected action.

                     else
                        Call_With_Same_Target :=
                          Potentially_Blocking_External_Call
                            (SC.E, Protected_Type);

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
                                  (Call_With_Same_Target.External_Callee),

                              F3       =>
                                Direct_Mapping_Id (Protected_Subp),

                              Tag      => Potentially_Blocking_In_Protected,
                              Severity => High_Check_Kind,
                              Vertex   => V);
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
         if Is_Attribute_Old (N) then
            declare
               Vars : constant Flow_Id_Sets.Set :=
                 Get_All_Variables
                   (N,
                    Scope                => FA.B_Scope,
                    Target_Name          => Null_Flow_Id,
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
           (FA.Spec_Entity,
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
               --  represented as either null or block statements with the
               --  original call statement kept in the Original_Node.

               return Nkind (N) in N_Block_Statement | N_Null_Statement
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

   ---------------------------------------------
   -- Check_Output_Constant_After_Elaboration --
   ---------------------------------------------

   procedure Check_Output_Constant_After_Elaboration
     (FA : in out Flow_Analysis_Graphs)
   is
      Globals : Global_Flow_Ids;

   begin
      --  Ignore packages (which have no Global contracts) and functions with
      --  no side effects (which have no global outputs).

      if Ekind (FA.Spec_Entity) in E_Procedure | E_Entry | E_Task_Type
        or else Is_Function_With_Side_Effects (FA.Spec_Entity)
      then

         Get_Globals (Subprogram => FA.Spec_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         --  Check that the program unit does not modify variables that have
         --  Constant_After_Elaboration set.

         for Output of Globals.Outputs loop
            if Is_Constant_After_Elaboration (Output) then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "constant after elaboration & " &
                              "must not be an output of subprogram &",
                  Severity => High_Check_Kind,
                  N        => Find_Global (FA.Spec_Entity, Output),
                  F1       => Output,
                  F2       => Direct_Mapping_Id (FA.Spec_Entity),
                  SRM_Ref  => "6.1.4(22)",
                  Tag      => Not_Constant_After_Elaboration);
            end if;
         end loop;
      end if;
   end Check_Output_Constant_After_Elaboration;

   -------------------------------------------------
   -- Check_Calls_With_Constant_After_Elaboration --
   -------------------------------------------------

   procedure Check_Calls_With_Constant_After_Elaboration
     (FA : in out Flow_Analysis_Graphs)
   is
      procedure Check_Subprogram (E : Entity_Id; Err_Loc : Node_Id);
      --  Inspects globals of subprogram E to detect violations of SPARK RM
      --  6.1.4(22).

      ----------------------
      -- Check_Subprogram --
      ----------------------

      procedure Check_Subprogram (E : Entity_Id; Err_Loc : Node_Id) is

         procedure Emit_Check (Globals : Flow_Id_Sets.Set);
         --  Emit check when SRM 6.1.4(22) is violated

         ----------------
         -- Emit_Check --
         ----------------

         procedure Emit_Check (Globals : Flow_Id_Sets.Set) is
         begin
            for Global of Globals loop
               if Is_Constant_After_Elaboration (Global) then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "subprogram & with global constant " &
                                 "after elaboration & must not be called " &
                                 "during elaboration of &",
                     Severity => High_Check_Kind,
                     N        => Err_Loc,
                     F1       => Direct_Mapping_Id (E),
                     F2       => Global,
                     F3       => Direct_Mapping_Id (FA.Spec_Entity),
                     SRM_Ref  => "6.1.4(22)",
                     Tag      => Not_Constant_After_Elaboration);
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

         Emit_Check (Globals.Inputs);
         Emit_Check (Globals.Proof_Ins);
      end Check_Subprogram;

   --  Start of processing for Check_Constant_After_Elaboration

   begin
      --  Check calls of a package elaboration

      if Is_Library_Level_Entity (FA.Spec_Entity) then
         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);
            begin
               for SC of Atr.Subprogram_Calls loop
                  if Ekind (SC.E) not in E_Package | E_Subprogram_Type then
                     Check_Subprogram (SC.E, Atr.Error_Location);
                  end if;
               end loop;
            end;
         end loop;
      end if;
   end Check_Calls_With_Constant_After_Elaboration;

   -----------------------------------------
   -- Check_Function_For_Volatile_Effects --
   -----------------------------------------

   procedure Check_Function_For_Volatile_Effects
     (FA : in out Flow_Analysis_Graphs)
   is
      Volatile_Effect_Found    : Boolean := False;
      Volatile_Effect_Allowed  : Boolean;
      Volatile_Effect_Expected : Boolean;

      procedure Report_Erroneous_Volatility;
      --  Emits a high check for every volatile variable found in a
      --  nonvolatile function.

      ---------------------------------
      -- Report_Erroneous_Volatility --
      ---------------------------------

      procedure Report_Erroneous_Volatility is
      begin
         --  Issue error if dealing with nonvolatile function; SPARK RM
         --  7.1.3(8).
         --  There are two cases to consider:
         --  1) the function uses volatile variables, and
         --  2) the function accesses state which may be externally modified.

         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop

            --  Note that it is not useful to emit errors for the the 'Final
            --  globals associated with the function specification.

            if FA.CFG.Get_Key (V).Variant /= Final_Value then
               declare
                  Atr : V_Attributes renames FA.Atr (V);

                  Repr : Flow_Id;
                  --  For constituents that are visible in the body but must be
                  --  represented by their encapsulating abstract state in the
                  --  spec, this will be the abstract state that represents
                  --  them.

               begin
                  for Var of To_Entire_Variables (Atr.Variables_Used) loop

                     --  Case 1: Volatile variables

                     if Is_Volatile (Var) then
                        pragma Assert (Present (Atr.Error_Location));
                        Error_Msg_Flow
                           (FA       => FA,
                            Msg      =>
                               "volatile variable & cannot act as global " &
                               "item of nonvolatile function &",
                            N        => Atr.Error_Location,
                            F1       => Var,
                            F2       => Direct_Mapping_Id (FA.Spec_Entity),
                            Severity => Error_Kind,
                            Tag      =>
                               Non_Volatile_Function_With_Volatile_Effects,
                            Vertex   => V);

                     --  Case 2: We up-project the variable to determine if
                     --  it is a constituent of an abstract state.

                     else
                        Repr := Up_Project (Var, FA.S_Scope);

                        if Repr /= Var
                           and then Is_Volatile (Repr)
                        then
                           Error_Msg_Flow
                              (FA       => FA,
                               Msg      =>
                                  "external state abstraction & " &
                                  "of variable & cannot act as global item " &
                                  "of nonvolatile function & ",
                               N        => Atr.Error_Location,
                               F1       => Repr,
                               F2       => Var,
                               F3       => Direct_Mapping_Id
                                  (FA.Spec_Entity),
                               Severity => Error_Kind,
                               Tag      =>
                                  Non_Volatile_Function_With_Volatile_Effects,
                               Vertex   => V);
                        end if;
                     end if;
                  end loop;
               end;
            end if;
         end loop;

      end Report_Erroneous_Volatility;

   --  Start of processing for Check_Function_For_Volatile_Effects

   begin
      if Ekind (FA.Spec_Entity) /= E_Function then

         --  If we are not dealing with a function then we have nothing to do
         --  here.

         return;
      end if;

      Volatile_Effect_Allowed :=
        (if Is_Protected_Type (Scope (FA.Spec_Entity))
         then Is_Volatile_For_Internal_Calls (FA.Spec_Entity)
         else Is_Volatile_Function (FA.Spec_Entity));

      Volatile_Effect_Expected :=
        Sem_Prag.Is_Enabled_Pragma
          (Get_Pragma (FA.Spec_Entity, Pragma_Volatile_Function));

      declare
         Globals : Global_Flow_Ids;

      begin
         --  Populate global sets using (possibly generated) Global from the
         --  function specification.

         Get_Globals (Subprogram => FA.Spec_Entity,
                      Scope      => FA.S_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         --  Check globals for volatiles. Sets Proof_Ins and Inputs are
         --  disjoint, so it is more efficient to process them separately
         --  instead of computing their union. The global Outputs of a
         --  function, after sanity checks, are known to be empty.

         --  The function is volatile if one of its parameters or its result
         --  type is of a volatile type for reading.

         Volatile_Effect_Found :=
            (for some F of Globals.Proof_Ins => Is_Volatile_For_Reading (F))
              or else
            (for some F of Globals.Inputs => Is_Volatile_For_Reading (F))
              or else
            Has_Effectively_Volatile_Profile (FA.Spec_Entity);

         pragma Assert
           (if not Is_Function_With_Side_Effects (FA.Spec_Entity)
            then Globals.Outputs.Is_Empty);
      end;

      --  Emit messages about nonvolatile functions with volatile effects
      if not Volatile_Effect_Allowed
         and then Volatile_Effect_Found
      then
         Report_Erroneous_Volatility;
      end if;

      --  Emit messages about volatile function without volatile effects

      if Volatile_Effect_Expected
         and then not Volatile_Effect_Found
      then
         Error_Msg_Flow
            (FA       => FA,
             Msg      => "volatile function & has no volatile effects",
             Severity => Warning_Kind,
             N        => FA.Spec_Entity,
             F1       => Direct_Mapping_Id (FA.Spec_Entity),
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
               when Suspends_On      =>
                  "multiple tasks might suspend on suspension object &",
               when Unsynch_Accesses =>
                  "possible data race when accessing variable &");
         --  Main error message

         Msg_Owner_String : constant String :=
           (case Owning_Kind is
               when Suspends_On      => "with task &",
               when Unsynch_Accesses => "task & accesses &");
         --  Supplementary message

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

               function Get_Msg_Object (Object : Entity_Name)
                                        return Entity_Name;
               --  Find the outermost encapsulating state of Object whose fully
               --  refined constituents are owned by all Owner_Types.

               --------------------
               -- Get_Msg_Object --
               --------------------

               function Get_Msg_Object (Object : Entity_Name)
                                        return Entity_Name
               is
                  Current_Abstraction  : Entity_Name := Object;
                  Current_Constituents : Name_Sets.Set;
                  --  While going from the innermost object to its outermost
                  --  encapsulating state, these will represent the current
                  --  context.

                  Previous_Abstraction : Entity_Name;
                  --  If we get to an abstract state that doesn't satisfy the
                  --  criteria, then we will return the previous one that we
                  --  have seen (which necessarily satisfy the criteria).

               begin
                  --  The outer loop will terminate because state abstraction
                  --  is finite and cannot have circular dependence.
                  loop
                     if GG_Is_Constituent (Current_Abstraction) then
                        Previous_Abstraction := Current_Abstraction;
                        Current_Abstraction  :=
                          GG_Encapsulating_State (Current_Abstraction);
                        Current_Constituents :=
                          GG_Expand_Abstract_State (Current_Abstraction);
                        --  GG_Expand_Abstract_State can hypothetically return
                        --  the input state, but it shouldn't in this case -
                        --  and if it did, the loop may become infinite.
                        pragma Assert (not Current_Constituents.Contains
                                       (Current_Abstraction));
                     else
                        --  This is the outermost encapsulating state of
                        --  Object, which may be Object itself.
                        return Current_Abstraction;
                     end if;

                     --  Check the criteria for all tasks that own the Object

                     for Owner of Owner_Types loop
                        if not Current_Constituents.Is_Subset
                          (Of_Set => Tasking_Objects (Owning_Kind, Owner))
                        then
                           return Previous_Abstraction;
                        end if;
                     end loop;

                     --  If the criteria are satisfied then retry the
                     --  encapsulating abstract state, if any.
                  end loop;
               end Get_Msg_Object;

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

                     --  Report common contested state at the most abstract
                     --  level of abstraction wherever possible.
                     Report_Violations (Object     => Get_Msg_Object (Object),
                                        Owners     => Owners,
                                        Msg_Object => Msg,
                                        Msg_Owner  => Msg_Owner_String,
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

         Conts : Message_Lists.List;
         Dummy : Boolean;
         --  Dummy variable needed for Error_Msg_Flow

      begin
         --  Print all the queueing tasks objects that we found. Include the
         --  Object to ensure that when multiple objects need to be reported
         --  for contention by the same tasks, they are all reported separately
         --  (otherwise messages get suppresed giving a confusing output.)
         for Task_Obj of Owners loop
            Conts.Append
              (Create
                 (Substitute_Message
                      (Msg_Owner,
                       Msg_Node,
                       F1 => Magic_String_Id (Task_Obj.Name),
                       F2 => Magic_String_Id (Object))));
         end loop;

         Error_Msg_Flow
           (E             => Msg_Node,
            N             => Msg_Node,
            Suppressed    => Dummy,
            Severity      => Severity,
            Tag           => Concurrent_Access,
            Msg           => Msg_Object,
            F1            => Magic_String_Id (Object),
            SRM_Ref       => SRM_Ref,
            Continuations => Conts);
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
      if not Is_Protected_Operation (FA.Spec_Entity) then
         return;
      end if;

      Preconditions := Get_Precondition_Expressions (FA.Spec_Entity);

      --  Populate global sets
      Get_Globals (Subprogram => FA.Spec_Entity,
                   Scope      => FA.S_Scope,
                   Classwide  => False,
                   Globals    => Globals);

      --  Add Proof_Ins to Reads
      Globals.Inputs.Union (Globals.Proof_Ins);

      for Precondition of Preconditions loop
         declare
            VU : constant Flow_Id_Sets.Set :=
              Get_All_Variables (Precondition,
                                 Scope                => FA.S_Scope,
                                 Target_Name          => Null_Flow_Id,
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
                     F2       => Direct_Mapping_Id (FA.Spec_Entity),
                     SRM_Ref  => "9(10)",
                     Tag      => Reference_To_Non_CAE_Variable);
               end if;
            end loop;
         end;
      end loop;
   end Check_CAE_In_Preconditions;

   -----------------------------
   -- Check_Always_Terminates --
   -----------------------------

   procedure Check_Always_Terminates (FA : in out Flow_Analysis_Graphs) is

      Enclosing_Subp : constant Entity_Id :=
        Subprograms.Enclosing_Subprogram (FA.Spec_Entity);

      Spec_Entity_Id : constant Flow_Id :=
        Direct_Mapping_Id (FA.Spec_Entity);

      Aspect : constant String :=
        (if Has_Implicit_Always_Terminates (FA.Spec_Entity)
         then "implicit "
         else "")
        & "aspect Always_Terminates";

      Proved : Boolean := True;

      function Check_Msg (Reason : String) return String is
        (Aspect & " on & could be incorrect, " & Reason);

   begin
      if Get_Termination_Condition (FA.Spec_Entity) = (Static, True) then

         --  If all paths in subprogram raise exceptions or, more importantly,
         --  call procedures with No_Return, then the CFG will be pruned. We
         --  already emit a check about this, but still we must suppress the
         --  positive message about terminating contract being correct.

         if FA.Has_Only_Exceptional_Paths then
            Proved := False;
         end if;

         for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
            declare
               Atr : V_Attributes renames FA.Atr (V);
            begin
               --  Ignore vertices coming from elaboration of nested packages

               if not Atr.In_Nested_Package then
                  if Atr.Is_Neverending then
                     Proved := False;
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => Check_Msg ("loop might be nonterminating"),
                        Fix      => "add loop variant in the loop body",
                        Severity => Medium_Check_Kind,
                        N        => Atr.Error_Location,
                        F1       => Spec_Entity_Id,
                        Tag      => Subprogram_Termination,
                        Vertex   => V);
                  end if;

                  for SC of Atr.Subprogram_Calls loop

                     --  Elaboration of nested packages always terminates; deal
                     --  with it early, because some of the routines used later
                     --  rightly do not expect to be called with packages.

                     if Ekind (SC.E) = E_Package then
                        null;

                     elsif Ekind (SC.E) = E_Subprogram_Type then

                        Proved := False;
                        Error_Msg_Flow
                          (FA          => FA,
                           Msg         => Check_Msg
                                            ("call via access-to-subprogram " &
                                             "might be nonterminating"),
                           Explanation => (if Is_Function_Type (SC.E)
                                           then "call could hide recursive " &
                                                "calls"
                                           else ""),
                           Severity    => Medium_Check_Kind,
                           N           => Atr.Error_Location,
                           F1          => Spec_Entity_Id,
                           Tag         => Subprogram_Termination,
                           Vertex      => V);

                     elsif Nkind (SC.N) in N_Subprogram_Call
                       and then Flow_Classwide.Is_Dispatching_Call (SC.N)
                     then

                        Proved := False;
                        Error_Msg_Flow
                          (FA          => FA,
                           Msg         => Check_Msg
                                            ("dispatching call to & " &
                                             "might be nonterminating"),
                           Explanation => (if Nkind (SC.N) = N_Function_Call
                                           then "call could hide recursive " &
                                                "calls"
                                           else ""),
                           Severity    => Medium_Check_Kind,
                           N           => Atr.Error_Location,
                           F1          => Spec_Entity_Id,
                           F2          => Direct_Mapping_Id (SC.E),
                           Tag         => Subprogram_Termination,
                           Vertex      => V);

                     --  If the analyzed subprogram, its Always_Terminates
                     --  aspect cannot be trusted. A message is emitted if the
                     --  subprogram has no Subprogram_Variant aspect.

                     elsif SC.E = FA.Spec_Entity then

                        if not Has_Subprogram_Variant (SC.E) then
                           Proved := False;
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => Check_Msg
                                            ("subprogram is recursive"),
                              Fix      => "annotate & with a " &
                                          "Subprogram_Variant aspect",
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              F1       => Spec_Entity_Id,
                              FF1      => Spec_Entity_Id,
                              Tag      => Subprogram_Termination,
                              Vertex   => V);
                        end if;

                     else

                        --  If the analyzed subprogram and the called
                        --  subprogram are mutually recursive, both
                        --  Always_Terminates aspects cannot be trusted. A
                        --  message is emitted if both subprograms have no
                        --  Subprogram_Variant aspect. In case where
                        --  FA.Spec_Entity is a nested package, we check the
                        --  Subprogram_Variant of its enclosing subprogram.

                        if Mutually_Recursive (FA.Spec_Entity, SC.E)
                          and then not Has_Subprogram_Variant (SC.E)
                          and then not Has_Subprogram_Variant (Enclosing_Subp)
                        then

                           Proved := False;
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => Check_Msg
                                           ("& and & are mutually recursive"),
                              Fix      => "annotate & and & with " &
                                          "Subprogram_Variant aspects",
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              F1       => Spec_Entity_Id,
                              F2       => Direct_Mapping_Id (FA.Spec_Entity),
                              F3       => Direct_Mapping_Id (SC.E),
                              FF1      => Direct_Mapping_Id (FA.Spec_Entity),
                              FF2      => Direct_Mapping_Id (SC.E),
                              Tag      => Subprogram_Termination,
                              Vertex   => V);

                        --  If the called subprogram is potentially
                        --  nonreturning for a reason that is not recursion,
                        --  a message is emitted. In this case, the
                        --  Always_Terminates aspect is trusted.

                        elsif
                          Get_Termination_Condition (SC.E) = (Static, False)
                             or else
                             (Get_Termination_Condition (SC.E).Kind
                                = Unspecified
                                   and then
                               (Calls_Potentially_Nonreturning_Subprogram
                                  (SC.E)
                                or else Is_Directly_Nonreturning (SC.E)))
                        then
                           Proved := False;
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => Check_Msg ("call to & might be " &
                                                     "nonterminating"),
                              Fix      =>
                                (if Get_Termination_Condition (SC.E).Kind =
                                   Unspecified
                                 then
                                   "annotate & with aspect Always_Terminates"
                                 else ""),
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              F1       => Spec_Entity_Id,
                              F2       => Direct_Mapping_Id (SC.E),
                              FF1      => Direct_Mapping_Id (SC.E),
                              Tag      => Subprogram_Termination,
                              Vertex   => V);
                        end if;
                     end if;
                  end loop;

                  for N of Atr.Indirect_Calls loop

                     --  We emit messages for dispatching equalities like we do
                     --  for other dispatching calls.

                     if Calls_Dispatching_Equality (N) then
                        Proved := False;
                        Error_Msg_Flow
                          (FA          => FA,
                           Msg         => Check_Msg
                             ("indirect dispatching call to record equality " &
                              "might be nonterminating"),
                           Explanation => ("call could hide recursive " &
                                           "calls"),
                           Severity    => Medium_Check_Kind,
                           N           => Atr.Error_Location,
                           F1          => Spec_Entity_Id,
                           Tag         => Subprogram_Termination,
                           Vertex      => V);

                     --  Otherwise, we check whether the analyzed subprogram is
                     --  recursive with the called primitive equalities.

                     else
                        declare
                           Typ   : constant Node_Id :=
                             (if Nkind (N) = N_Function_Call
                              then Etype (First_Actual (N))
                              else Etype (Left_Opnd (N)));

                           Funcs : constant Node_Sets.Set :=
                             Called_Primitive_Equalities
                               (Typ,
                                Nkind (N) in N_Op);
                        begin
                           for E of Funcs loop
                              if E = FA.Spec_Entity then

                                 Proved := False;
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Msg      => Check_Msg
                                      ("subprogram is recursive"),
                                    Severity => Medium_Check_Kind,
                                    N        => Atr.Error_Location,
                                    F1       => Spec_Entity_Id,
                                    Tag      => Subprogram_Termination,
                                    Vertex   => V);

                              elsif Mutually_Recursive (FA.Spec_Entity, E) then
                                 Proved := False;
                                 Error_Msg_Flow
                                   (FA       => FA,
                                    Msg      => Check_Msg
                                      ("& and record equality on type & are " &
                                       "mutually recursive"),
                              Severity => Medium_Check_Kind,
                                    N        => Atr.Error_Location,
                                    F1       => Spec_Entity_Id,
                                    F2       => Direct_Mapping_Id
                                      (FA.Spec_Entity),
                                    F3       => Direct_Mapping_Id (Typ),
                                    Tag      => Subprogram_Termination,
                                    Vertex   => V);

                              end if;
                           end loop;
                        end;
                     end if;
                  end loop;
               end if;
            end;
         end loop;

         if Proved and then Is_Subprogram_Or_Entry (FA.Spec_Entity) then
            Error_Msg_Flow (FA       => FA,
                            Msg      =>
                              Aspect & " on & has been proved, "
                              & "subprogram will terminate",
                            Severity => Info_Kind,
                            N        => FA.Spec_Entity,
                            F1       => Spec_Entity_Id,
                            Tag      => Subprogram_Termination);
         end if;
      end if;
   end Check_Always_Terminates;

   ----------------------------
   -- Check_Ghost_Terminates --
   ----------------------------

   procedure Check_Ghost_Terminates (FA : in out Flow_Analysis_Graphs) is
   begin
      --  We are only interested in calls originating from non-ghost entities.
      --  Also, if the termination condition of the caller is statically true,
      --  then we check the termination conditon of its callees anyway, so
      --  messages emitted here would be duplicates.

      if Is_Ghost_Entity (FA.Spec_Entity)
        or else Get_Termination_Condition (FA.Spec_Entity) = (Static, True)
      then
         return;
      end if;

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
         begin
            --  Ignore vertices coming from elaboration of nested packages

            if not Atr.In_Nested_Package then
               for SC of Atr.Subprogram_Calls loop
                  if Is_Ghost_Entity (SC.E) then
                     if Get_Termination_Condition (SC.E, Compute => True) =
                          (Static, False)
                     then
                        --  For calls via access-to-subprogram don't mention
                        --  the subprogram name (both because it wouldn't be
                        --  terribly useful and because it could be an itype).
                        --  Also, don't emit a possible fix, because
                        --  access-to-subprograms types cannot be annotated
                        --  with Always_Terminates anyway.

                        if Ekind (SC.E) = E_Subprogram_Type then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "call to ghost access-to-subprogram " &
                                "might be nonterminating",
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              Tag      => Subprogram_Termination,
                              Vertex   => V);

                        --  For calls to ordinary subprograms with statically
                        --  false termination the check is certain and clear,
                        --  so no need to offer a fix.

                        elsif Get_Termination_Condition (SC.E) =
                                (Static, False)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "call to ghost subprogram & is nonterminating",
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              F1       => Direct_Mapping_Id (SC.E),
                              Tag      => Subprogram_Termination,
                              Vertex   => V);
                        else
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "call to ghost subprogram & " &
                                "might be nonterminating",
                              Fix      =>
                                "annotate & with aspect Always_Terminates",
                              Severity => Medium_Check_Kind,
                              N        => Atr.Error_Location,
                              F1       => Direct_Mapping_Id (SC.E),
                              FF1      => Direct_Mapping_Id (SC.E),
                              Tag      => Subprogram_Termination,
                              Vertex   => V);
                        end if;
                     end if;
                  end if;
               end loop;
            end if;
         end;
      end loop;
   end Check_Ghost_Terminates;

   ----------------------------------------
   -- Check_Constant_Global_Contracts --
   ----------------------------------------

   procedure Check_Constant_Global_Contracts (E : Entity_Id) is
      procedure Check_Constant_Global (G : Entity_Id);
      --  Check whether a single entity G is allowed to appear as a Global
      --  or Depends input.

      ---------------------------
      -- Check_Constant_Global --
      ---------------------------

      procedure Check_Constant_Global (G : Entity_Id) is
      begin
         if Ekind (G) = E_Constant
           and then not Is_Access_Variable (Etype (G))
           and then not Has_Variable_Input (G)
         then
            declare
               The_Global_In : constant Flow_Id := Direct_Mapping_Id (G);
               Unused        : Boolean;
            begin
               Error_Msg_Flow
                 (E          => E,
                  Msg        => "& not allowed as input to &",
                  N          => Find_Global (S => E, F => The_Global_In),
                  Suppressed => Unused,
                  F1         => The_Global_In,
                  F2         => Direct_Mapping_Id (E),
                  SRM_Ref    => "6.1.4(16)",
                  Tag        => Global_Wrong,
                  Severity   => Medium_Check_Kind);
            end;
         end if;
      end Check_Constant_Global;

      --  Local variables

      Spec_Globals : Raw_Global_Nodes;

   begin
      --  Only apply this check to entities with user supplied Global/Depends

      if Has_User_Supplied_Globals (E) then
         Spec_Globals := Contract_Globals (E);

         --  Constants can only appear as Inputs and Proof_Ins (which are
         --  disjoint so we iterate over them separately); frontend already
         --  rejects them if they appear as Outputs.

         for G of Spec_Globals.Proof_Ins loop
            Check_Constant_Global (G);
         end loop;

         for G of Spec_Globals.Inputs loop
            Check_Constant_Global (G);
         end loop;
      end if;
   end Check_Constant_Global_Contracts;

end Flow.Analysis;
