------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2017, Altran UK Limited                 --
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

with Ada.Text_IO;

with Elists;                      use Elists;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Output;                      use Output;
with Restrict;                    use Restrict;
with Rident;                      use Rident;
with Sem_Aux;                     use Sem_Aux;
with Sem_Type;                    use Sem_Type;
with Sem_Util;                    use Sem_Util;
with Sinput;                      use Sinput;
with Snames;                      use Snames;

with Common_Iterators;            use Common_Iterators;
with Gnat2Why.Annotate;           use Gnat2Why.Annotate;
with Gnat2Why_Args;               use Gnat2Why_Args;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Frame_Conditions;      use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with SPARK_Util;                  use SPARK_Util;
with VC_Kinds;                    use VC_Kinds;

with Flow.Analysis.Antialiasing;
with Flow.Analysis.Sanity;
with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;            use Flow_Error_Messages;
with Flow_Refinement;                use Flow_Refinement;
with Flow_Utility;                   use Flow_Utility;
with Flow_Utility.Initialization;    use Flow_Utility.Initialization;

with Why;

package body Flow.Analysis is

   Debug_Trace_Depends     : constant Boolean := False;
   --  Enable this to show the specified and computed dependency relation.

   Debug_Trace_Check_Reads : constant Boolean := False;
   --  Enable this to show in/unin status of each vertex/variable examines.

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Get_Line
     (G   : Flow_Graphs.Graph;
      M   : Attribute_Maps.Map;
      V   : Flow_Graphs.Vertex_Id;
      Sep : Character := ':') return String;
   --  Obtain the location for the given vertex as in "foo.adb:12".

   procedure Write_Vertex_Set
     (FA       : Flow_Analysis_Graphs;
      Set      : Vertex_Sets.Set;
      Filename : String);
   --  Write a trace file for GPS. Do not generate a trace file if there is no
   --  sloc, or a single sloc in the vertex set, as this is not useful.

   function Find_Global
     (S : Entity_Id;
      F : Flow_Id) return Node_Or_Entity_Id
   with Pre => Ekind (S) in Entry_Kind     |
                            E_Function     |
                            E_Package      |
                            E_Package_Body |
                            E_Procedure    |
                            E_Task_Type;
   --  Find the global F in the Global, Refined_Global, or Initializes aspect
   --  of S. If it is not there (perhaps because it comes from computed
   --  globals) just return S which is a good fallback location for error
   --  reports.

   function Get_Initial_Vertex (G : Flow_Graphs.Graph;
                                F : Flow_Id)
                                return Flow_Graphs.Vertex_Id
   with Pre  => F.Variant = Normal_Use,
        Post => Get_Initial_Vertex'Result = Flow_Graphs.Null_Vertex
                  or else G.Get_Key (Get_Initial_Vertex'Result).Variant in
                            Initial_Value | Initial_Grouping;
   --  Returns the vertex id which represents the initial value for F

   function Get_Final_Vertex (G : Flow_Graphs.Graph;
                              F : Flow_Id)
                              return Flow_Graphs.Vertex_Id
   with Pre  => F.Variant = Normal_Use,
        Post => G.Get_Key (Get_Final_Vertex'Result).Variant = Final_Value;
   --  Returns the vertex id which represents the final value for F

   function Is_Param_Of_Null_Subp_Of_Generic (E : Entity_Id)
                                              return Boolean
   with Pre => Nkind (E) in N_Entity;
   --  Returns True iff E is a parameter of a formal subprogram of a generic
   --  unit and the formal subprogram has null default.

   --------------------
   -- Error_Location --
   --------------------

   function Error_Location
     (G : Flow_Graphs.Graph;
      M : Attribute_Maps.Map;
      V : Flow_Graphs.Vertex_Id) return Node_Or_Entity_Id
   is
      Loc : constant Node_Or_Entity_Id := M (V).Error_Location;
   begin
      if Present (Loc) then
         return Loc;
      else
         declare
            K : Flow_Id renames G.Get_Key (V);
         begin
            case K.Kind is
               when Direct_Mapping | Record_Field =>
                  return Get_Direct_Mapping_Id (K);
               when others =>
                  raise Why.Unexpected_Node;
            end case;
         end;
      end if;
   end Error_Location;

   --------------
   -- Get_Line --
   --------------

   function Get_Line
     (G   : Flow_Graphs.Graph;
      M   : Attribute_Maps.Map;
      V   : Flow_Graphs.Vertex_Id;
      Sep : Character := ':') return String
   is
      N       : constant Node_Or_Entity_Id := Error_Location (G, M, V);
      SI      : constant Source_File_Index := Get_Source_File_Index (Sloc (N));
      Line_No : constant String :=
        Logical_Line_Number'Image (Get_Logical_Line_Number (Sloc (N)));
   begin
      return Get_Name_String (File_Name (SI)) & Sep &
        Line_No (2 .. Line_No'Last);
   end Get_Line;

   ----------------------
   -- Write_Vertex_Set --
   ----------------------

   procedure Write_Vertex_Set
     (FA       : Flow_Analysis_Graphs;
      Set      : Vertex_Sets.Set;
      Filename : String)
   is
      FD : Ada.Text_IO.File_Type;
   begin
      if Set.Length > 1 then
         Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Filename);

         for V of Set loop
            declare
               F : Flow_Id renames FA.PDG.Get_Key (V);
            begin
               if F.Kind = Direct_Mapping then
                  Ada.Text_IO.Put_Line (FD, Get_Line (FA.PDG, FA.Atr, V));
               end if;
            end;
         end loop;

         Ada.Text_IO.Close (FD);
      end if;
   end Write_Vertex_Set;

   ---------------------
   -- Global_Required --
   ---------------------

   procedure Global_Required
     (FA  : in out Flow_Analysis_Graphs;
      Var : Flow_Id)
   is
      First_Use : constant Node_Id :=
        First_Variable_Use
          (FA      => FA,
           Var     => Var,
           Kind    => Use_Any,
           Precise => True);

   begin
      pragma Assert (Nkind (First_Use) in N_Subprogram_Call);

      Error_Msg_Flow
        (FA       => FA,
         Msg      => "called subprogram & requires GLOBAL " &
           "aspect to make state & visible",
         N        => First_Use,
         F1       => Direct_Mapping_Id (Get_Called_Entity (First_Use)),
         F2       => Var,
         Severity => Error_Kind);
   end Global_Required;

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
                  if Nkind (N) in N_Identifier | N_Expanded_Name
                    and then Present (Entity (N))
                    and then Nkind (Entity (N)) in N_Entity
                    -- ??? workaround or something?
                    and then Unique_Entity (Entity (N)) = Target
                  then
                     Result := N;
                     return Abandon;
                  else
                     return OK;
                  end if;
               end Process;

               procedure Traverse is new Traverse_Proc (Process);

            begin
               case Ekind (S) is
                  when E_Package_Body =>
                     Traverse
                       (Get_Pragma (Spec_Entity (S), Pragma_Initializes));

                  when E_Package =>
                     Traverse (Get_Pragma (S, Pragma_Initializes));

                  when Entry_Kind | E_Function | E_Procedure | E_Task_Type =>
                     Traverse (Find_Contract (S, Pragma_Refined_Global));

                     if Result /= S then
                        return Result;
                     end if;

                     Traverse (Find_Contract (S, Pragma_Global));

                  when others =>
                     raise Program_Error;
               end case;

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
      Result : Flow_Graphs.Vertex_Id;
   begin
      --  Look for either the Initial_Value or Initial_Grouping variant
      Result := G.Get_Vertex (Change_Variant (F, Initial_Value));

      if Result = Flow_Graphs.Null_Vertex then
         return G.Get_Vertex (Change_Variant (F, Initial_Grouping));
      else
         return Result;
      end if;
   end Get_Initial_Vertex;

   ----------------------
   -- Get_Final_Vertex --
   ----------------------

   function Get_Final_Vertex
     (G : Flow_Graphs.Graph;
      F : Flow_Id)
      return Flow_Graphs.Vertex_Id
   is
   begin
      return G.Get_Vertex (Change_Variant (F, Final_Value));
   end Get_Final_Vertex;

   ------------------------
   -- First_Variable_Use --
   ------------------------

   function First_Variable_Use
     (N        : Node_Id;
      FA       : Flow_Analysis_Graphs;
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
      --  This function sets First_Use to the given node if it
      --  contains the variable we're looking for. If not, we abort
      --  the search.

      -----------------
      -- Search_Expr --
      -----------------

      function Search_Expr (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) not in N_Subprogram_Call
                           | N_Entry_Call_Statement
                           | N_Expanded_Name
                           | N_Identifier
                           | N_Selected_Component
         then
            --  Calling Get_Variables can be very slow. Let's only do it on
            --  nodes that actually make sense to flag up in an check/info
            --  message from flow; i.e. nodes that describe a
            --  variable/constant or might use a global.
            return OK;
         elsif Get_Variables (N,
                              Scope                => Scope,
                              Local_Constants      => FA.Local_Constants,
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
      end Search_Expr;

      procedure Search_Expression is new Traverse_Proc (Search_Expr);
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
                                          FA      => FA,
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
               N        => Find_Global (FA.Analyzed_Entity, R),
               F1       => R,
               F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
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

      for R of Globals.Reads loop
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
      Vars_Used  : Flow_Id_Sets.Set;
      Vars_Known : Flow_Id_Sets.Set;

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
               when Kind_Subprogram   => "6.1.4(13)",
               when Kind_Package
                  | Kind_Package_Body => "7.1.5(11)",
               when Kind_Task         => raise Program_Error);

         begin
            if Refined then
               Vars_Known := To_Entire_Variables (FA.All_Vars);
            else
               case FA.Kind is
                  when Kind_Subprogram =>
                     --  We need to assemble the variables known from the spec:
                     --  these are parameters (both explicit and implicit) and
                     --  globals.

                     Vars_Known :=
                       To_Flow_Id_Set (Get_Formals (FA.Analyzed_Entity));

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

                        for F of Globals.Reads loop
                           Vars_Known.Insert (Change_Variant (F, Normal_Use));
                        end loop;

                        for F of Globals.Writes loop
                           Vars_Known.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;

                  when Kind_Package | Kind_Package_Body =>
                     Vars_Known := Flow_Id_Sets.Empty_Set;

                     for F of To_Entire_Variables (FA.Visible_Vars) loop
                        case F.Kind is
                           when Direct_Mapping =>
                              Vars_Known.Union
                                (To_Flow_Id_Set
                                   (Down_Project
                                      (Get_Direct_Mapping_Id (F),
                                       FA.S_Scope)));

                           when Magic_String =>
                              Vars_Known.Insert (F);

                           when others =>
                              raise Program_Error;
                        end case;
                     end loop;

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
                       Scope                => Get_Flow_Scope (Expr),
                       Local_Constants      => FA.Local_Constants,
                       Fold_Functions       => False,
                       Reduced              => True,
                       Use_Computed_Globals => True))
                 - Quantified_Variables (Expr);

               for Var of Vars_Used loop
                  if not Vars_Known.Contains (Var) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& must be listed in the " &
                                      Aspect_To_Fix & " aspect of &",
                        SRM_Ref  => SRM_Ref,
                        N        => First_Variable_Use (N       => Expr,
                                                        FA      => FA,
                                                        Scope   => FA.B_Scope,
                                                        Var     => Var,
                                                        Precise => False),
                        F1       => Var,
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Severity => High_Check_Kind);
                     Sane := False;

                  elsif FA.Kind in Kind_Package | Kind_Package_Body
                    and then Is_Library_Level_Entity (FA.Analyzed_Entity)
                    and then not Is_Initialized_At_Elaboration (Var,
                                                                FA.B_Scope)
                  then

                     --  To check an initial_condition aspect, we make sure
                     --  that all variables mentioned are also mentioned in
                     --  an initializes aspect.

                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& must be initialized at elaboration",
                        N        => First_Variable_Use (N       => Expr,
                                                        FA      => FA,
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

      Written_Entire_Vars : Flow_Id_Sets.Set;
      Unwritten_Vars      : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

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
        (Is_Concurrent_Type
           (Etype (Get_Direct_Mapping_Id (Entire_Variable (F)))));

   --  Start of processing for Find_Unwritten_Exports

   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : Flow_Id      renames FA.PDG.Get_Key (V);
            A_Final : V_Attributes renames FA.Atr (V);

            Unwritten : Boolean;

         begin
            if F_Final.Variant = Final_Value
              and then A_Final.Is_Export
            then

               --  We have a final use vertex which is an export that has
               --  a single in-link. If this in-link is its initial value
               --  then clearly we do not set this output on any path.

               Unwritten := False;
               if FA.PDG.In_Neighbour_Count (V) = 1 then
                  declare
                     F_Initial : Flow_Id renames
                       FA.PDG.Get_Key (FA.PDG.Parent (V));
                     A_Initial : V_Attributes renames
                       FA.Atr (FA.PDG.Parent (V));
                  begin
                     if F_Initial.Variant = Initial_Value
                       and then A_Initial.Is_Import
                       and then
                         Change_Variant (F_Initial, Final_Value) = F_Final
                     then
                        Unwritten := True;
                     end if;
                  end;
               end if;

               if Unwritten then
                  Unwritten_Vars.Include (V);
               else
                  Written_Entire_Vars.Include (Entire_Variable (F_Final));
               end if;
            end if;
         end;
      end loop;

      for V of Unwritten_Vars loop
         declare
            F_Final : Flow_Id      renames FA.PDG.Get_Key (V);
            A_Final : V_Attributes renames FA.Atr (V);
         begin
            if not Written_Entire_Vars.Contains (Entire_Variable (F_Final))
            then
               --  We inhibit messages for variables that:
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
                             (Get_Direct_Mapping_Id (F_Final)))
               then
                  null;

               else
                  if A_Final.Is_Global then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& is not modified, could be INPUT",
                        N        => Find_Global (FA.Analyzed_Entity, F_Final),
                        F1       => Entire_Variable (F_Final),
                        Tag      => Inout_Only_Read,
                        Severity => Warning_Kind,
                        Vertex   => V);
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

      ------------------
      -- Is_Final_Use --
      ------------------

      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean is
         Atr : V_Attributes renames FA.Atr (V);

      begin
         return
           (case FA.PDG.Get_Key (V).Variant is
                when Final_Value => Atr.Is_Export,
                when Normal_Use  => Atr.Is_Exceptional_Branch,
                when others      => False)
              or else Atr.Is_Assertion;
      end Is_Final_Use;

      Suppressed         : Flow_Id_Sets.Set;
      --  Entire variables appearing in a "null => Blah" dependency relation;
      --  for these we suppress the ineffective import warning.

      Considered_Imports : Flow_Id_Sets.Set;
      Considered_Objects : Flow_Id_Sets.Set;
      --  Entire variables considered for each of the two analyses

      Used               : Flow_Id_Sets.Set;
      --  Entire bariables used at least once (even if this use is not
      --  effective).

      Effective          : Flow_Id_Sets.Set;
      --  Entire variables whose at least part is used (for example an
      --  individual component of a record, or the bounds of an unconstrained
      --  array) to determine the final value of at least one export.

      Unused             : Flow_Id_Sets.Set;
      Ineffective        : Flow_Id_Sets.Set;

   --  Start of processing for Find_Ineffective_Imports_And_Unused_Objects

   begin
      --  If this subprogram has only exceptional paths, then we already have a
      --  high check for this. We don't issue any other messages as they
      --  distract from the real issue.

      if FA.Has_Only_Exceptional_Paths then
         return;
      end if;

      --  We look at the null depends (if one exists). For any variables
      --  mentioned there, we suppress the ineffective import warning by
      --  putting them to Suppressed.

      if FA.Kind = Kind_Subprogram and then Present (FA.Depends_N) then
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

      pragma Assert_And_Cut (True);

      --  Detect imports that do not contribute to at least one export and
      --  objects that are never used.

      pragma Assert (Considered_Imports.Is_Empty and then
                     Considered_Objects.Is_Empty and then
                     Used.Is_Empty               and then
                     Effective.Is_Empty);

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Var : Flow_Id      renames FA.PDG.Get_Key (V);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Var.Variant = Initial_Value
              and then Var.Kind /= Synthetic_Null_Export
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
                  --  Using bounds or discriminants marks the entire variable
                  --  as used; not using them has no effect. However, this
                  --  only applies to out parameters; for in out parameters the
                  --  value of the entire variable itself has to be used and
                  --  uses of bounds and discriminants are completely ignored.

                  if Bound_Or_Discr
                    and then Atr.Mode = Mode_In_Out
                  then
                     null;
                  else
                     --  Determine effective and considered imports

                     if Atr.Is_Initialized and Atr.Is_Import then

                        --  Check if we're effective. If not, note that we at
                        --  least partially have used the entire variable.

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
                           if FA.PDG.Get_Key (Final_V).Variant /= Final_Value
                             or else FA.PDG.In_Neighbour_Count (Final_V) > 1
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

      pragma Assert_And_Cut
        (Effective.Is_Subset (Of_Set => Considered_Imports) and then
         Used.Is_Subset      (Of_Set => Considered_Objects));

      --  Issue error messages. We can't do this when detecting, because
      --  detecting works on record components and we care about entire
      --  variables.

      --  First we deal with unused objects

      Unused := Considered_Objects - Used;

      for F of Unused loop
         declare
            V : constant Flow_Graphs.Vertex_Id :=
              Get_Initial_Vertex (FA.PDG, F);

         begin
            if FA.Atr (V).Is_Global then
               --  In generative mode we inhibit messages on globals
               if not FA.Is_Generative then
                  declare
                     Is_Var : constant Boolean := Is_Variable (F);
                     --  Issue a different errors for variables and constants

                     Msg : constant String :=
                       (if Is_Var
                        then "unused global &"
                        else "& cannot appear in Globals");

                     Severity : constant Msg_Severity :=
                       (if Is_Var
                        then Low_Check_Kind
                        else Medium_Check_Kind);

                  begin
                     --  We prefer the report the error on the subprogram, not
                     --  on the global.

                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => Msg,
                        N        => Find_Global (FA.Analyzed_Entity, F),
                        F1       => F,
                        Tag      => VC_Kinds.Unused,
                        Severity => Severity,
                        Vertex   => V);
                  end;
               end if;
            else
               --  We suppress this warning when:
               --  * we are dealing with a concurrent type or a component of a
               --    concurrent type
               --  * we are dealing with a null record
               --  * the variable has been marked either as Unreferenced or
               --    Unmodified or Unused
               --  * the variable is a formal parameter of a null subprogram of
               --    a generic unit.
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
                    or else Belongs_To_Concurrent_Type (F)
                    or else (Is_Type (E_Typ)
                             and then Is_Empty_Record_Type (E_Typ))
                    or else Has_Pragma_Un (E)
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

      --  Finally we deal with ineffective imports. We exclude items which are
      --  suppressed by a null derives and which have previously been flagged
      --  as unused. In the loop below we further exclude objects that are
      --  marked by a pragma Unreferenced or a pragma Unmodified or a pragma
      --  Unused.

      Ineffective := Considered_Imports - (Effective or Suppressed or Unused);

      for F of Ineffective loop
         declare
            V   : constant Flow_Graphs.Vertex_Id :=
              Get_Initial_Vertex (FA.PDG, F);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if F.Kind = Direct_Mapping
              and then (Has_Pragma_Un (Get_Direct_Mapping_Id (F))
                          or else
                        (In_Generic_Actual (Get_Direct_Mapping_Id (F)) and then
                         Scope_Within_Or_Same
                           (Scope (Get_Direct_Mapping_Id (F)),
                            FA.Spec_Entity)))
            then
               --  This variable is marked with a pragma Unreferenced, pragma
               --  Unused or pragma Unmodified so we do not warn here; also, we
               --  do not warn for ineffective declarations of constants in
               --  wrapper packages of generic subprograms. ??? maybe we want a
               --  separate check for them.
               null;
            elsif Atr.Mode = Mode_Proof then
               --  Proof_Ins are never ineffective imports, for now
               null;
            elsif Atr.Is_Global then
               if FA.Kind = Kind_Subprogram
                 and then not FA.Is_Generative
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      =>
                       (if Present (FA.B_Scope)
                        and then Is_Abstract_State (F)
                        and then FA.B_Scope.Part /= Body_Part
                        and then State_Refinement_Is_Visible
                                   (F, Body_Scope (FA.B_Scope))
                        then "non-visible constituents of & are not used " &
                              "- consider moving the subprogram to the " &
                              "package body and adding a Refined_Global"
                        else "unused initial value of &"),
                     N        => Find_Global (FA.Analyzed_Entity, F),
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
                  (Is_Concurrent_Type (Etype (Get_Direct_Mapping_Id (F)))
                     or else
                   Belongs_To_Concurrent_Type (F)
                     or else
                   (Is_Type (Etype (Get_Direct_Mapping_Id (F)))
                      and then
                      Is_Empty_Record_Type
                        (Etype (Get_Direct_Mapping_Id (F)))))
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
           and then Scope (E) not in FA.Analyzed_Entity | FA.Spec_Entity
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
                  Clause : Node_Id;
               begin
                  Clause := First (Context_Items (CUnit));
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
                                 " - Elaborate_All pragma required for &",
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
      --  Returns True if vertex V defines some variable that has
      --  property Async_Readers set.

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set;
      --  Find out why a given vertex is ineffective. A vertex is
      --  ineffective if the variable(s) defined by it are re-defined
      --  on all paths leading from it without being used. Thus all
      --  reachable vertices which also define at least one variable
      --  of that set (and do not use it), render the vertex
      --  ineffective.

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if from the given vertex V it is impossible to reach the
      --  end vertex.

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean;
      --  Checks if the given vertex V represents an externally visible
      --  outcome, i.e. is a final-use vertex that is also an export or
      --  a use vertex that branches to an exceptional path.

      function Is_In_Pragma_Un (S : Flow_Id_Sets.Set)
                                return Boolean;
      --  Checks if variables in the set Variables_Defined have been
      --  mentioned in a pragma Unmodified, Unused or Unreferenced.

      function Other_Fields_Are_Ineffective (V : Flow_Graphs.Vertex_Id)
                                             return Boolean;
      --  This function returns True if V corresponds to an assignment
      --  to a record field that has been introduced by a record split
      --  and the rest of the fields are ineffective.

      function Skip_Any_Conversions (N : Node_Or_Entity_Id)
                                     return Node_Or_Entity_Id;
      --  Skips any conversions (unchecked or otherwise) and jumps to
      --  the actual object.

      ------------------------------
      -- Defines_Async_Reader_Var --
      ------------------------------

      function Defines_Async_Reader_Var
        (V : Flow_Graphs.Vertex_Id)
         return Boolean
      is
      begin
         for Var_Def of FA.Atr (V).Variables_Defined loop
            declare
               Initial_Var : constant Flow_Id :=
                 Change_Variant (Var_Def, Final_Value);
            begin
               if Has_Async_Readers (Initial_Var) then
                  return True;
               end if;
            end;
         end loop;

         return False;
      end Defines_Async_Reader_Var;

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
                     Mask.Include (V);
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

      function Is_Any_Final_Use
        (V : Flow_Graphs.Vertex_Id)
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
      begin
         --  ??? not a case-expression-function because of a front-end bug;
         --  can be refactored once P308-025 is fixed.
         case FA.PDG.Get_Key (V).Variant is
            when Final_Value => return FA.Atr (V).Is_Export;
            when Normal_Use  => return FA.Atr (V).Is_Exceptional_Branch;
            when others      => return False;
         end case;
      end Is_Final_Use_Any_Export;

      ---------------------
      -- Is_In_Pragma_Un --
      ---------------------

      function Is_In_Pragma_Un (S : Flow_Id_Sets.Set)
                                return Boolean
      is
        (for some E of S =>
           E.Kind in Direct_Mapping | Record_Field
             and then Has_Pragma_Un (Get_Direct_Mapping_Id (E)));

      --------------------------
      -- Skip_Any_Conversions --
      --------------------------

      function Skip_Any_Conversions (N : Node_Or_Entity_Id)
                                     return Node_Or_Entity_Id
      is
         P : Node_Or_Entity_Id := N;
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
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            use Attribute_Maps;
            N         : Node_Id;
            Key       : Flow_Id renames FA.PDG.Get_Key (V);
            Atr       : V_Attributes renames FA.Atr (V);
            Mask      : Vertex_Sets.Set;
            Tag       : constant Flow_Tag_Kind := Ineffective;
            Tracefile : constant String := Fresh_Trace_File;
         begin
            if Atr.Is_Program_Node or
              Atr.Is_Parameter or
              Atr.Is_Global_Parameter
            then
               --  A vertex is ineffective if there is no path in the
               --  PDG to *any* final use vertex that is also an
               --  export.
               --
               --  If we analyse a package, we suppress this message
               --  if we don't have an initializes clause *and* the
               --  given vertex has an effect on any final use (export
               --  or otherwise).
               if
                 --  Basic check here
                 not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use_Any_Export'Access) and then

                 --  Suppression for dead code
                 not Is_Dead_End (V) and then

                 --  Suppression for package initializations
                 not Atr.Is_Package_Initialization and then

                 --  Suppression for packages without initializes
                 (if FA.Kind in Kind_Package | Kind_Package_Body
                    and then No (FA.Initializes_N)
                  then
                     not FA.PDG.Non_Trivial_Path_Exists
                      (V, Is_Any_Final_Use'Access)) and then

                 --  Suppression for vertices that talk about a variable
                 --  that is mentioned in a pragma Unused, Unmodified or
                 --  Unreferenced.
                 not Is_In_Pragma_Un (Atr.Variables_Defined) and then

                 --  Suppression for vertices that can lead to
                 --  abnormal termination and have had some of their
                 --  out edges removed.
                 not Atr.Is_Exceptional_Branch and then

                 --  Suppression for vertices that correspond to
                 --  an assignment to a record field, that comes
                 --  from a record split, while the rest of the
                 --  fields are not ineffective.
                 Other_Fields_Are_Ineffective (V) and then

                 --  Suppression for vertices that define a variable
                 --  that has Async_Readers set.
                 not Defines_Async_Reader_Var (V) and then

                 --  Suppression for vertices with assertion expressions
                 not Atr.Is_Assertion and then

                 --  Suppression for vertices that write to ghost variables
                 --  ??? Probably we want remove this suppression
                 not (for some Var of Atr.Variables_Defined =>
                         Is_Ghost_Object (Var)) and then

                 --  Suppression for ghost entities
                 not Is_Ghost_Entity (FA.Spec_Entity)
               then
                  Mask := Find_Masking_Code (V);
                  N    := Error_Location (FA.PDG, FA.Atr, V);

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
                              else
                                Atr.Parameter_Formal);

                           Printable_Target : constant Boolean :=
                             Is_Easily_Printable (Target);

                        begin
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => (if Printable_Target
                                            then "unused assignment to &"
                                            else "unused assignment"),
                              N         => Error_Location (FA.PDG, FA.Atr, V),
                              F1        => (if Printable_Target
                                            then Target
                                            else Null_Flow_Id),
                              Tag       => Tag,
                              Severity  => Warning_Kind,
                              Vertex    => V);
                        end;
                     end if;

                  elsif Nkind (N) = N_Assignment_Statement then
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "unused assignment",
                        N         => Error_Location (FA.PDG, FA.Atr, V),
                        Tag       => Tag,
                        Severity  => Warning_Kind,
                        Vertex    => V);

                  elsif Nkind (N) = N_Object_Declaration then
                     if not Constant_Present (N) then
                        --  This warning is ignored for local constants

                        if FA.Kind in Kind_Package | Kind_Package_Body
                          and then No (Find_In_Initializes
                                         (Defining_Identifier (N)))
                        then
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "initialization of &" &
                                           " is not mentioned in " &
                                           "Initializes contract",
                              N         => FA.Initializes_N,
                              F1        =>
                                Direct_Mapping_Id (Defining_Entity (N)),
                              Tag       => Tag,
                              Severity  => Warning_Kind,
                              Vertex    => V);
                        else
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "initialization of &" &
                                           " has no effect",
                              N         => Error_Location (FA.PDG, FA.Atr, V),
                              F1        =>
                                Direct_Mapping_Id (Defining_Entity (N)),
                              Tag       => Tag,
                              Severity  => Warning_Kind,
                              Vertex    => V);
                        end if;

                     end if;

                  else
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "statement has no effect",
                        Severity  => Warning_Kind,
                        N         => Error_Location (FA.PDG, FA.Atr, V),
                        Tag       => Tag,
                        Vertex    => V);

                  end if;

                  if not Mask.Is_Empty then
                     Write_Vertex_Set
                       (FA       => FA,
                        Set      => Mask,
                        Filename => Tracefile);
                  end if;
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
                           --  Flag the given node as "live".

      function Edge_Selector (A, B : Flow_Graphs.Vertex_Id) return Boolean;

      ---------------
      -- Flag_Live --
      ---------------

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
      begin
         Dead_Code.Exclude (V);
         TV := Flow_Graphs.Continue;
      end Flag_Live;

      -------------------
      -- Edge_Selector --
      -------------------

      function Edge_Selector (A, B : Flow_Graphs.Vertex_Id) return Boolean is
      begin
         case FA.CFG.Edge_Colour (A, B) is
            when EC_Default =>
               return True;
            when EC_Abend | EC_Inf | EC_Barrier =>
               return True;
            when others =>
               raise Program_Error;
         end case;
      end Edge_Selector;

   --  Start of processing for Find_Dead_Code

   begin
      --  Guilty until proven innocent.
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
         begin
            if Atr.Is_Program_Node or
              Atr.Is_Parameter or
              Atr.Is_Global_Parameter
            then
               Dead_Code.Include (V);
            end if;
         end;
      end loop;

      --  Discover live code
      FA.CFG.DFS (Start         => FA.Start_Vertex,
                  Include_Start => True,
                  Visitor       => Flag_Live'Access,
                  Edge_Selector => Edge_Selector'Access);

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
      Tracefile : constant String := Fresh_Trace_File;

      function Consider_Vertex (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Returns True iff V should be considered for uninitialized variables

      procedure Emit_Message (Var              : Flow_Id;
                              Vertex           : Flow_Graphs.Vertex_Id;
                              Is_Initialized   : Boolean;
                              Is_Uninitialized : Boolean)
      with Pre => (Is_Initialized or Is_Uninitialized)
                  and then not Is_Internal (Var);
      --  Produces an appropriately worded info/low/high message for the given
      --  variable Var at the given location Vertex.
      --
      --  Is_Initialized should be set if there is at least one sensible read
      --
      --  Is_Uninitialized should be set if there is at least one read from an
      --  uninitialized variable.
      --
      --  They can be both set, in which case we're most likely going to
      --  produce a medium check, but this is not always the case in loops.

      function Has_Only_Infinite_Execution (V_Final : Flow_Graphs.Vertex_Id)
                                            return Boolean;
      --  Returns True iff every path from V_Final going backwards in the CFG
      --  contains an infinite loop.

      function Expand_Initializes return Node_Sets.Set
      with Pre  => FA.Kind in Kind_Package | Kind_Package_Body
                   and then Present (FA.Initializes_N),
           Post => (for all E of Expand_Initializes'Result =>
                      Ekind (E) in E_Abstract_State | E_Constant | E_Variable);
      --  Returns entities that appear (either directly or as immediate
      --  constituents of an abstract state) on the LHS of the Initializes
      --  contract of the currently analyzed package.
      --
      --  In other words, this routine down-projects the LHS of the Initializes
      --  contract to the scope of the private part or body of the current
      --  package (depending on the SPARK_Mode barrier).

      procedure Mark_Definition_Free_Path
        (From      : Flow_Graphs.Vertex_Id;
         To        : Flow_Graphs.Vertex_Id;
         Var       : Flow_Id;
         V_Allowed : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
      --  Write a trace file that marks the path From -> To which does not
      --  define Var. If V_Allowed is set, then the path that we return is
      --  allowed to contain V_Allowed even if V_Allowed does set Var.

      function Mentioned_On_Generated_Initializes
        (Var : Flow_Id)
         return Boolean
      with Pre => Ekind (FA.Analyzed_Entity) in E_Package | E_Package_Body;
      --  Returns True if Var is mentioned on the LHS of a generated
      --  Initializes aspect.

      procedure Might_Be_Defined_In_Other_Path
        (V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id;
         Found     : out Boolean;
         V_Error   : out Flow_Graphs.Vertex_Id);
      --  Sets Found when the variable corresponding to V_Initial is defined on
      --  a path that leads to V_Use. V_Error is the vertex where the message
      --  should be emitted.

      ---------------------
      -- Consider_Vertex --
      ---------------------

      function Consider_Vertex (V : Flow_Graphs.Vertex_Id) return Boolean is
         V_Key : Flow_Id      renames FA.PDG.Get_Key (V);
         V_Atr : V_Attributes renames FA.Atr (V);
      begin
         --  Ignore exceptional paths
         if V_Atr.Is_Exceptional_Path then
            return False;
         end if;

         --  Ignore synthetic null output and ???
         if V_Key.Variant = Final_Value
           and then (not V_Atr.Is_Export or else Synthetic (V_Key))
         then
            return False;
         end if;

         --  If we reach this point then the Vertex must be considered
         return True;
      end Consider_Vertex;

      ------------------
      -- Emit_Message --
      ------------------

      procedure Emit_Message (Var              : Flow_Id;
                              Vertex           : Flow_Graphs.Vertex_Id;
                              Is_Initialized   : Boolean;
                              Is_Uninitialized : Boolean)
      is
         type Msg_Kind is (Init, Unknown, Err);

         V_Key         : Flow_Id renames FA.PDG.Get_Key (Vertex);

         V_Initial     : constant Flow_Graphs.Vertex_Id :=
           FA.PDG.Get_Vertex (Change_Variant (Var, Initial_Value));

         Kind          : Msg_Kind :=
           (if Is_Initialized and Is_Uninitialized then Unknown
            elsif Is_Initialized                   then Init
            else                                        Err);

         N             : Node_Or_Entity_Id;
         Msg           : Unbounded_String;

         V_Error       : Flow_Graphs.Vertex_Id;
         V_Goal        : Flow_Graphs.Vertex_Id;
         V_Allowed     : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

         Is_Final_Use  : constant Boolean := V_Key.Variant = Final_Value;
         Is_Global     : constant Boolean := FA.Atr (V_Initial).Is_Global;
         Default_Init  : constant Boolean := Is_Default_Initialized (Var);
         Is_Function   : constant Boolean := Is_Function_Entity (Var);

      begin
         case Kind is
            when Unknown | Err =>
               declare
                  Defined_Elsewhere : Boolean;
               begin
                  Might_Be_Defined_In_Other_Path
                    (V_Initial => V_Initial,
                     V_Use     => Vertex,
                     Found     => Defined_Elsewhere,
                     V_Error   => V_Error);
                  if not Defined_Elsewhere then
                     --  Upgrade check to high if a more detailed path
                     --  analysis shows we can't feasibly set it.
                     Kind := Err;
                  end if;
               end;
            when others =>
               V_Error := Vertex;
         end case;

         --  Assemble appropriate message for failed initialization. We deal
         --  with a bunch of special cases first, but if they don't trigger we
         --  create the standard message.
         if Kind = Init then
            Msg := To_Unbounded_String ("initialization of & proved");
         elsif Is_Function then
            Msg := To_Unbounded_String ("function & does not return on ");
            if Has_Only_Infinite_Execution (Vertex) then
               Append (Msg, "any path");
            else
               Append (Msg, "some paths");
            end if;
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
            V_Goal    := V_Error;
            V_Allowed := Vertex;
            N         := Error_Location (FA.PDG, FA.Atr, V_Error);
            --  When the message is a failed check we produce a more precise
            --  location (but this can be very expensive, see the test for
            --  Q824-007 for a good example). So, if the message is an info
            --  message AND we use --report=fail (the default), we don't do
            --  this refinement.
            if not (Kind = Init and Gnat2Why_Args.Report_Mode = GPR_Fail) then
               N := First_Variable_Use
                 (N        => N,
                  FA       => FA,
                  Scope    => FA.B_Scope,
                  Var      => Var,
                  Precise  => True,
                  Targeted => True);
            end if;
         elsif Is_Global then
            V_Goal := FA.Helper_End_Vertex;
            N      := Find_Global (FA.Analyzed_Entity, Var);
         else
            V_Goal := V_Error;
            N      := FA.Atr (Vertex).Error_Location;
         end if;

         if Kind = Init and then Is_Function_Entity (Var) then
            pragma Assert (Get_Direct_Mapping_Id (Var) = FA.Analyzed_Entity);
            --  We special case this, so we don't emit "X" is initialized
            --  messages for the "variable" that represents the function's
            --  result.
            return;
         end if;

         Error_Msg_Flow
           (FA        => FA,
            Tracefile => Tracefile,
            Msg       => To_String (Msg),
            N         => N,
            F1        => Var,
            F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
            Tag       => Uninitialized,
            Severity  => (case Kind is
                          when Init    => Info_Kind,
                          when Unknown => (if Default_Init
                                           then Low_Check_Kind
                                           else Medium_Check_Kind),
                          when Err     => (if Default_Init
                                           then Medium_Check_Kind
                                           else High_Check_Kind)),
            Vertex    => Vertex);

         if Is_Constituent (Var)
           and then Kind in Unknown | Err
           and then FA.Kind in Kind_Package | Kind_Package_Body
           and then Present (FA.Initializes_N)
         then
            Error_Msg_Flow
              (FA           => FA,
               Tracefile    => Tracefile,
               Msg          => "initialization of & is specified @",
               N            => N,
               F1           => Direct_Mapping_Id
                                 (Encapsulating_State
                                    (Get_Direct_Mapping_Id (Var))),
               F2           => Direct_Mapping_Id (FA.Initializes_N),
               Tag          => Uninitialized,
               Severity     => (case Kind is
                                when Init    => Info_Kind,
                                when Unknown => Medium_Check_Kind,
                                when Err     => High_Check_Kind),
               Vertex       => Vertex,
               Continuation => True);
         end if;

         if Kind /= Init then
            Mark_Definition_Free_Path
              (From      => FA.Start_Vertex,
               To        => V_Goal,
               Var       => Var,
               V_Allowed => V_Allowed);
         end if;

         --  In case of a subprogram with an output global which is actually
         --  used as an input in its body, we add more information to the error
         --  message.
         if Kind = Err
           and then not Default_Init
           and then Is_Global
         then
            Error_Msg_Flow (FA           => FA,
                            Msg          => "& is not an input " &
                              "in the Global contract of subprogram " &
                              "#",
                            Severity     => High_Check_Kind,
                            N            => N,
                            F1           => Var,
                            F2           =>
                              Direct_Mapping_Id (FA.Spec_Entity),
                            Tag          => Uninitialized,
                            Continuation => True);

            declare
               Msg : constant String :=
                 (if Has_Async_Readers (Var)
                  then "either make & an input in the Global contract or " &
                    "write to it before use"
                  else "either make & an input in the Global contract or " &
                    "initialize it before use");

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
      end Emit_Message;

      ------------------------
      -- Expand_Initializes --
      ------------------------

      function Expand_Initializes return Node_Sets.Set is
         Results : Node_Sets.Set;

         Initializes : constant Dependency_Maps.Map :=
           Parse_Initializes (FA.Spec_Entity, Null_Flow_Scope);
         --  Initializes aspect parsed into Flow_Ids; the second parameter is
         --  irrelevant, as Parse_Initializes only uses it when dealing with a
         --  generated contract.

      begin
         for Clause in Initializes.Iterate loop
            declare
               E : constant Entity_Id :=
                 Get_Direct_Mapping_Id (Dependency_Maps.Key (Clause));
            begin
               --  ??? here we basically down-project items on the LHS to the
               --  FA.B_Scope, but we can't reuse the Down_Project routine yet,
               --  as it trumps over the SPARK_Mode barrier (which is explained
               --  in a ??? comment there).

               if Ekind (E) = E_Abstract_State then
                  if Entity_Body_In_SPARK (FA.Spec_Entity) then
                     if not Has_Null_Refinement (E) then
                        for C of Iter (Refinement_Constituents (E)) loop
                           Results.Insert (C);
                        end loop;
                     end if;
                  elsif Private_Spec_In_SPARK (FA.Spec_Entity) then
                     for C of Iter (Part_Of_Constituents (E)) loop
                        Results.Insert (C);
                     end loop;
                  end if;
               else
                  pragma Assert (Ekind (E) in E_Constant | E_Variable);
                  Results.Insert (E);
               end if;
            end;
         end loop;

         return Results;
      end Expand_Initializes;

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

      -------------------------------
      -- Mark_Definition_Free_Path --
      -------------------------------

      procedure Mark_Definition_Free_Path
        (From      : Flow_Graphs.Vertex_Id;
         To        : Flow_Graphs.Vertex_Id;
         Var       : Flow_Id;
         V_Allowed : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex)
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
            elsif V /= V_Allowed
              and then FA.Atr (V).Variables_Defined.Contains (Var)
            then
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
               Path.Include (V);
            end if;
         end Add_Loc;

      --  Start of processing for Mark_Definition_Free_Path

      begin
         FA.CFG.Shortest_Path (Start         => From,
                               Allow_Trivial => False,
                               Search        => Are_We_There_Yet'Access,
                               Step          => Add_Loc'Access);

         --  When dealing with an exceptional path it is possible for
         --  Path_Found to be false.

         if Path_Found then
            Write_Vertex_Set (FA       => FA,
                              Set      => Path,
                              Filename => Tracefile);
         end if;
      end Mark_Definition_Free_Path;

      ----------------------------------------
      -- Mentioned_On_Generated_Initializes --
      ----------------------------------------

      function Mentioned_On_Generated_Initializes
        (Var : Flow_Id)
         return Boolean
      is
         (GG_Get_Initializes (FA.Spec_Entity, FA.S_Scope).Contains (Var));

      ------------------------------------
      -- Might_Be_Defined_In_Other_Path --
      ------------------------------------

      procedure Might_Be_Defined_In_Other_Path
        (V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id;
         Found     : out Boolean;
         V_Error   : out Flow_Graphs.Vertex_Id)
      is
         The_Var : constant Flow_Id :=
           Change_Variant (FA.PDG.Get_Key (V_Initial), Normal_Use);

         The_Var_Is_Array : constant Boolean :=
           (The_Var.Kind = Direct_Mapping
              and then Is_Type (Etype (Get_Direct_Mapping_Id (The_Var)))
              and then Has_Array_Type
                         (Etype (Get_Direct_Mapping_Id (The_Var))))
           or else
           (The_Var.Kind = Record_Field
              and then The_Var.Facet = Normal_Part
              and then Is_Type (Etype (The_Var.Component.Last_Element))
              --  ??? how Etype might return a non-type?
              and then Has_Array_Type
                         (Etype (The_Var.Component.Last_Element)));
         --  True if The_Var refers to an array

         Use_Vertex_Points_To_Itself : constant Boolean :=
           (for some V of FA.PDG.Get_Collection (V_Use,
                                                 Flow_Graphs.Out_Neighbours)
              => V = V_Use);
         --  True if V_Use belongs to V_Use's Out_Neighbours

         Use_Execution_Is_Unconditional : constant Boolean :=
           (for some V of FA.PDG.Get_Collection (V_Use,
                                                 Flow_Graphs.In_Neighbours)
              => V = FA.Start_Vertex);
         --  True if FA.Start_Vertex is among the In_Neighbours of V_Use in the
         --  PDG (in other words, there is no control dependence on V).

         function Find_Explicit_Use_Vertex return Flow_Graphs.Vertex_Id;
         --  Find a vertex that explicitly uses The_Var and hangs off vertex
         --  V_Use in the CFG. If such a node does NOT exist, then Null_Vertex
         --  is returned.

         function Start_To_V_Def_Without_V_Use
           (V_Def : Flow_Graphs.Vertex_Id)
            return Boolean;
         --  Returns True if there exists a path in the CFG from Start to V_Def
         --  that does not cross V_Use.

         procedure Vertex_Defines_Variable
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Checks if V defines the The_Var
         --
         --  Sets Found

         ------------------------------
         -- Find_Explicit_Use_Vertex --
         ------------------------------

         function Find_Explicit_Use_Vertex return Flow_Graphs.Vertex_Id is
            V_Exp_Use : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

            procedure Found_V_Exp_Use
              (V  : Flow_Graphs.Vertex_Id;
               TV : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Stops the DFS search when we reach a vertex that contains
            --  The_Var in its Variables_Explicitly_Used set.

            ---------------------
            -- Found_V_Exp_Use --
            ---------------------

            procedure Found_V_Exp_Use
              (V  : Flow_Graphs.Vertex_Id;
               TV : out Flow_Graphs.Simple_Traversal_Instruction)
            is
            begin
               if V = V_Use then
                  TV := Flow_Graphs.Skip_Children;
               elsif V /= Flow_Graphs.Null_Vertex
                 and then FA.Atr (V).Variables_Defined.Contains (The_Var)
               then
                  TV := Flow_Graphs.Skip_Children;
               elsif V /= Flow_Graphs.Null_Vertex
                 and then FA.CFG.Get_Key (V).Variant /= Final_Value
                 and then
                   FA.Atr (V).Variables_Explicitly_Used.Contains (The_Var)
               then
                  V_Exp_Use := V;
                  TV := Flow_Graphs.Abort_Traversal;
               else
                  TV := Flow_Graphs.Continue;
               end if;
            end Found_V_Exp_Use;

         --  Start of processing for Find_Explicit_Use_Vertex

         begin
            FA.CFG.DFS (Start         => V_Use,
                        Include_Start => False,
                        Visitor       => Found_V_Exp_Use'Access,
                        Reversed      => False);

            return V_Exp_Use;
         end Find_Explicit_Use_Vertex;

         ----------------------------------
         -- Start_To_V_Def_Without_V_Use --
         ----------------------------------

         function Start_To_V_Def_Without_V_Use
           (V_Def : Flow_Graphs.Vertex_Id)
            return Boolean
         is
            Path_Exists : Boolean := False;

            procedure Found_V_Def
              (V  : Flow_Graphs.Vertex_Id;
               TV : out Flow_Graphs.Simple_Traversal_Instruction);
            --  Stops the DFS search when we reach V_Def and skips the children
            --  of V_Use.

            -----------------
            -- Found_V_Def --
            -----------------

            procedure Found_V_Def
              (V  : Flow_Graphs.Vertex_Id;
               TV : out Flow_Graphs.Simple_Traversal_Instruction)
            is
            begin
               if V = V_Use then
                  TV := Flow_Graphs.Skip_Children;
               elsif V = V_Def then
                  Path_Exists := True;
                  TV := Flow_Graphs.Abort_Traversal;
               else
                  TV := Flow_Graphs.Continue;
               end if;
            end Found_V_Def;

         --  Start_To_V_Def_Without_V_Use

         begin
            FA.CFG.DFS (Start         => FA.Start_Vertex,
                        Include_Start => False,
                        Visitor       => Found_V_Def'Access,
                        Reversed      => False);

            return Path_Exists;
         end Start_To_V_Def_Without_V_Use;

         -----------------------------
         -- Vertex_Defines_Variable --
         -----------------------------

         procedure Vertex_Defines_Variable
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
         begin
            if V = FA.Start_Vertex or else V = V_Use then

               --  If we reach the start vertex (remember, this traversal is
               --  going backwards through the CFG) or ourselves, then we
               --  should look for another path.

               TV := Flow_Graphs.Skip_Children;

            else
               TV := Flow_Graphs.Continue;
               if FA.Atr (V).Variables_Defined.Contains (The_Var) then

                  --  OK, so this vertex V does define The_Var. There are a few
                  --  cases where we can possibly issue a warning instead of an
                  --  error.

                  if Start_To_V_Def_Without_V_Use (V_Def => V) then
                     --  There is a path from start -> this definition V that
                     --  does not use V (but subsequenty reaches V).

                     Found := True;
                     TV    := Flow_Graphs.Abort_Traversal;

                  elsif not Use_Execution_Is_Unconditional then
                     --  If the execution of v_use is predicated on something
                     --  else, then there might be a path that defines the_var
                     --  first.

                     Found := True;
                     TV    := Flow_Graphs.Abort_Traversal;
                  end if;
               end if;

            end if;

         end Vertex_Defines_Variable;

      --  Start of processing for Might_Be_Defined_In_Other_Path

      begin
         --  Initialize V_Error to V_Use; we shall change it later if required.
         --  Ditto for Found.

         Found   := False;
         V_Error := V_Use;

         --  Check if there might be some path that defines the variable before
         --  we use it.

         FA.CFG.DFS (Start         => V_Use,
                     Include_Start => False,
                     Visitor       => Vertex_Defines_Variable'Access,
                     Reversed      => True);

         --  Arrays that are partially defined have an implicit dependency on
         --  themselves. For this check, we cannot depend on the Variables_Used
         --  because they capture this implicit dependency. Instead, we use
         --  Variables_Explicitly_Used.

         if not Found and then Use_Vertex_Points_To_Itself then
            case The_Var.Kind is
               when Direct_Mapping | Record_Field =>
                  --  Check if node corresponds to an array.
                  if The_Var_Is_Array
                    and then not FA.Atr (V_Use).
                      Variables_Explicitly_Used.Contains (The_Var)
                  then
                     --  We set Found and we then check if there exists a
                     --  vertex that explicitly uses The_Var, if so, we set
                     --  V_Error to that vertex.

                     Found := True;

                     declare
                        Tmp_V : constant Flow_Graphs.Vertex_Id :=
                          Find_Explicit_Use_Vertex;
                     begin
                        if Tmp_V /= Flow_Graphs.Null_Vertex then
                           V_Error := Tmp_V;
                        end if;
                     end;
                  end if;

               when Magic_String | Synthetic_Null_Export =>
                  null;

               when Null_Value =>
                  raise Why.Unexpected_Node;
            end case;
         end if;
      end Might_Be_Defined_In_Other_Path;

      --  Local variables:

      Expanded_Initializes : constant Node_Sets.Set :=
        (if FA.Kind in Kind_Package | Kind_Package_Body
           and then Present (FA.Initializes_N)
         then Expand_Initializes
         else Node_Sets.Empty_Set);
      --  Objects that appear (either directly or via an abstract state) in LHS
      --  of the Initializes contract of the currently analyzed pacakge, if
      --  any.
      --
      --  Note: expanding the Initializes contract is much simpler and more
      --  robust than locating an object there (or rather an abstract state
      --  that contains such an object). Also, expansion saves us from dealing
      --  with anomalies like Part_Of in private child units.

   --  Start of processing for Find_Use_Of_Uninitialized_Variables

   begin
      --  If this subprogram has only exceptional paths, then we already have a
      --  high check for this. We don't issue any other messages as they
      --  distract from the real issue.

      if FA.Has_Only_Exceptional_Paths then
         return;
      end if;

      --  We look at all vertices except for:
      --     * exceptional ones and
      --     * synthetic null output
      for V of FA.DDG.Get_Collection (Flow_Graphs.All_Vertices) loop

         if Consider_Vertex (V) then
            --  For each used variable...
            for Var_Used of FA.Atr (V).Variables_Used loop
               declare
                  Is_Uninitialized : Boolean := False;
                  Is_Initialized   : Boolean := False;

                  Initial_Value_Of_Var_Used : Flow_Graphs.Vertex_Id renames
                    FA.DDG.Get_Vertex
                      (Change_Variant (Var_Used, Initial_Value));

                  Final_Value_Of_Var_Used : Flow_Graphs.Vertex_Id renames
                    FA.DDG.Get_Vertex
                      (Change_Variant (Var_Used, Final_Value));

               begin
                  if FA.Atr (Initial_Value_Of_Var_Used).Is_Initialized

                    --  Skip this check for objects written when elaborating a
                    --  package, unless they appear in the explicit Initializes
                    --  contract. For them we either emit an "info:
                    --  initialization proved" message here, or an error in
                    --  Check_Initializes_Contract.
                    or else
                      (Final_Value_Of_Var_Used = V
                         and then
                       FA.Kind in Kind_Package | Kind_Package_Body
                         and then
                       not Expanded_Initializes.Contains
                              (Get_Direct_Mapping_Id (Var_Used)))

                    --  Skip obvious messages about initialization of constants

                    or else
                      Is_Constant (Var_Used)

                    --  Skip messages about initialization of internal objects,
                    --  assuming that they are created by the frontend inlining
                    --  and if they would cause access to an uninitialized
                    --  objects then we should get an error when analyzing
                    --  the inlined subprogram.
                    or else
                      Is_Internal (Var_Used)

                    --  Skip annoying message about initialization of records
                    --  that carry no data.

                    or else
                      (Var_Used.Kind in Direct_Mapping | Record_Field
                       and then
                         ((Is_Type (Etype (Get_Direct_Mapping_Id (Var_Used)))
                             and then
                           (Is_Empty_Record_Type
                              (Etype (Get_Direct_Mapping_Id (Var_Used)))))
                            or else
                            (Var_Used.Kind = Record_Field
                             and then Var_Used.Facet = Normal_Part
                             and then
                             Is_Empty_Record_Type
                               (Get_Type
                                  (Var_Used,
                                   Get_Flow_Scope
                                     (Get_Direct_Mapping_Id (Var_Used)))))))

                  then
                     --  ... we either do nothing because it is safe, or...
                     null;

                  else
                     --  ... we check the in-neighbours in the DDG and see if
                     --  they define it. We record initialized / uninitialized
                     --  reads accordingly.
                     --
                     for V_Def of
                       FA.DDG.Get_Collection (V, Flow_Graphs.In_Neighbours)
                     loop
                        declare
                           Def_Key : Flow_Id renames FA.DDG.Get_Key (V_Def);
                           Def_Atr : V_Attributes renames FA.Atr (V_Def);
                        begin
                           if Def_Key.Variant = Initial_Value
                             and then
                               Change_Variant (Def_Key, Normal_Use) = Var_Used
                           then
                              --  We're using the initial value
                              if Def_Atr.Is_Initialized then
                                 Is_Initialized   := True;
                              else
                                 Is_Uninitialized := True;
                              end if;
                           elsif Def_Atr.Variables_Defined.Contains (Var_Used)
                             or else Def_Atr.Volatiles_Read.Contains (Var_Used)
                           then
                              --  We're using a previously written value
                              Is_Initialized := True;
                           end if;
                        end;
                     end loop;

                     --  Some debug output before we issue the message
                     if Debug_Trace_Check_Reads then
                        Write_Str ("@" & FA.DDG.Vertex_To_Natural (V)'Img);
                        if Is_Initialized then
                           Write_Str (" INIT");
                        end if;
                        if Is_Uninitialized then
                           Write_Str (" DIRTY");
                        end if;
                        Write_Str (" :");
                        Print_Flow_Id (Var_Used);
                     end if;

                     Emit_Message (Var              => Var_Used,
                                   Vertex           => V,
                                   Is_Initialized   => Is_Initialized,
                                   Is_Uninitialized => Is_Uninitialized);
                  end if;
               end;
            end loop;
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

   -------------------------------------------
   --  Find_Exports_Derived_From_Proof_Ins  --
   -------------------------------------------

   procedure Find_Exports_Derived_From_Proof_Ins
     (FA : in out Flow_Analysis_Graphs)
   is
      function Path_Leading_To_Proof_In_Dependency
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id) return Vertex_Sets.Set;
      --  Returns a set of vertices that highlight the path in the CFG
      --  where the export depends on a Proof_In.

      ------------------------------------------
      --  Path_Leading_To_Proof_In_Dependency --
      ------------------------------------------

      function Path_Leading_To_Proof_In_Dependency
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id) return Vertex_Sets.Set
      is
         function Vertices_Between_From_And_To
           (From      : Flow_Graphs.Vertex_Id;
            To        : Flow_Graphs.Vertex_Id;
            CFG_Graph : Boolean := False) return Vertex_Sets.Set;
         --  Returns the smallest set of vertices that make up a path from
         --  "From" to "To" (excluding vertices "From" and "To"). By default
         --  it operates on the PDG graph. If CFG_Graph is set to True then it
         --  operates on the CFG.

         ------------------------------------
         --  Vertices_Between_From_And_To  --
         ------------------------------------

         function Vertices_Between_From_And_To
           (From      : Flow_Graphs.Vertex_Id;
            To        : Flow_Graphs.Vertex_Id;
            CFG_Graph : Boolean := False) return Vertex_Sets.Set
         is
            Vertices : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

            procedure Add_Loc (V : Flow_Graphs.Vertex_Id);
            --  Step procedure for Shortest_Path

            procedure Are_We_There_Yet
              (V           : Flow_Graphs.Vertex_Id;
               Instruction : out Flow_Graphs.Traversal_Instruction);
            --  Visitor procedure for Shortest_Path

            ---------------
            --  Add_Loc  --
            ---------------

            procedure Add_Loc (V : Flow_Graphs.Vertex_Id) is
            begin
               if V /= To
                 and then V /= From
                 and then (if CFG_Graph
                             then FA.CFG.Get_Key (V).Kind
                             else FA.PDG.Get_Key (V).Kind) = Direct_Mapping
               then
                  Vertices.Include (V);
               end if;
            end Add_Loc;

            ------------------------
            --  Are_We_There_Yet  --
            ------------------------

            procedure Are_We_There_Yet
              (V           : Flow_Graphs.Vertex_Id;
               Instruction : out Flow_Graphs.Traversal_Instruction)
            is
            begin
               if V = To then
                  Instruction := Flow_Graphs.Found_Destination;
               else
                  Instruction := Flow_Graphs.Continue;
               end if;
            end Are_We_There_Yet;

         --  Start of processing for Vertices_Between_Proof_In_And_Export

         begin
            if CFG_Graph then
               FA.CFG.Shortest_Path (Start         => From,
                                     Allow_Trivial => False,
                                     Search        => Are_We_There_Yet'Access,
                                     Step          => Add_Loc'Access);
            else
               FA.PDG.Shortest_Path (Start         => From,
                                     Allow_Trivial => False,
                                     Search        => Are_We_There_Yet'Access,
                                     Step          => Add_Loc'Access);
            end if;

            return Vertices;
         end Vertices_Between_From_And_To;

         Vertices_To_Cover : constant Vertex_Sets.Set :=
           Vertices_Between_From_And_To (From => From,
                                         To   => To);
         Path              : Vertex_Sets.Set := Vertices_To_Cover;
         Start             : Flow_Graphs.Vertex_Id;

      --  Start of processing for Path_Leading_To_Proof_In_Dependency

      begin
         --  Sanity check that we do not have an empty set.
         pragma Assert (not Vertices_To_Cover.Is_Empty);

         Start := FA.Start_Vertex;
         for Vert of Vertices_To_Cover loop
            Path.Union (Vertices_Between_From_And_To (From      => Start,
                                                      To        => Vert,
                                                      CFG_Graph => True));
            Start := Vert;
         end loop;

         return Path;
      end Path_Leading_To_Proof_In_Dependency;

   --  Start of processing for Find_Exports_Derived_From_Proof_Ins

   begin
      --  For ghost subprograms we do NOT need to do this check
      if Is_Ghost_Entity (FA.Analyzed_Entity) then
         return;
      end if;

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
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.Atr (V).Mode = Mode_Proof
                     then
                        declare
                           Tracefile      : constant String :=
                             Fresh_Trace_File;

                           Vertices_Trail : constant Vertex_Sets.Set :=
                             Path_Leading_To_Proof_In_Dependency
                               (From => V,
                                To   => Get_Final_Vertex (FA.PDG, Output));

                        begin
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "export & must not depend " &
                                           "on Proof_In &",
                              SRM_Ref   => "6.1.4(17)",
                              N         => Find_Global (FA.Analyzed_Entity,
                                                        Input),
                              F1        => Output,
                              F2        => Input,
                              Severity  => Medium_Check_Kind,
                              Tag       => Export_Depends_On_Proof_In);

                           Write_Vertex_Set
                             (FA       => FA,
                              Set      => Vertices_Trail,
                              Filename => Tracefile);
                        end;
                     end if;
                  end;
               end loop;
            end if;

         end;
      end loop;
   end Find_Exports_Derived_From_Proof_Ins;

   ---------------------------------
   -- Find_Hidden_Unexposed_State --
   ---------------------------------

   procedure Find_Hidden_Unexposed_State (FA : in out Flow_Analysis_Graphs) is
      Pkg_Spec : constant Node_Id := Package_Specification (FA.Spec_Entity);
      Pkg_Body : constant Node_Id := Package_Body (FA.Spec_Entity);

      procedure Check_Hidden_State_Variables_And_Missing_Part_Of
        (E : Entity_Id)
        with Pre => Ekind (E) in E_Constant | E_Variable
                    and not Is_Internal (E)
                    and not Is_Part_Of_Concurrent_Object (E);
      --  Emits a message if:
      --  * a state variable is not mentioned as a constituent of an abstract
      --    state when it should be;
      --  * a state variable is missing the Part_Of indicator which is required
      --    by SPARK RM 7.2.6(2-3).

      procedure Traverse_Declarations (L : List_Id);

      ------------------------------------------------------
      -- Check_Hidden_State_Variables_And_Missing_Part_Of --
      ------------------------------------------------------

      procedure Check_Hidden_State_Variables_And_Missing_Part_Of
        (E : Entity_Id)
      is
         State : constant Entity_Id := Encapsulating_State (E);
      begin
         --  Find state variable that is a Part_Of some state, but not listed
         --  in its refinement.
         if Is_Constituent (E)
           and then Refinement_Exists (State)
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

         --  Detect hidden variables in the private part of a package or in the
         --  package body that are not part of any refinement.
         if Ekind (E) = E_Variable
           and then not Is_Constituent (E)
           and then not In_Visible_Declarations (Enclosing_Declaration (E))
         then
            Error_Msg_Flow
              (FA       => FA,
               Msg      => "& needs to be a constituent of some state " &
                             "abstraction",
               N        => E,
               F1       => Direct_Mapping_Id (E),
               Tag      => Hidden_Unexposed_State,
               Severity => Medium_Check_Kind);
         end if;

         --  Look for constants with variable inputs without Part_Of that are
         --  declared:
         --  * in the private part of a package
         --  * in the visible part of a package declared immediately within
         --    the private part of a package
         --  * in the visible part of a private child.
         --  Those do require a Part_Of indicator as per SPARK RM 7.2.6(2-3).
         --
         --  ??? Note that here we don't use Is_Constituent but we directly
         --  check for a Part_Of indicator because at the moment Is_Constituent
         --  will return True when a constant declared in the private part of
         --  package is listed in the Refined_State but is missing a Part_Of
         --  indicator (and therefore Get_Pragma will return False). The
         --  condition with Get_Pragma could be replaced by Is_Constituent once
         --  the front end ticket (about fixing the above) will be addressed.
         if Ekind (E) = E_Constant
           and then not Present (Get_Pragma (E, Pragma_Part_Of))
           and then not In_Body_Declarations (Enclosing_Declaration (E))
         then
            declare
               S : constant Entity_Id := Scope (E);

               Msg : constant String :=
                 (if Is_Private_Descendant (S)
                  then "visible part of the private child"
                  else "private part of package");

               SRM_Ref : constant String :=
                 (if Is_Private_Descendant (S)
                  then "7.2.6(3)"
                  else "7.2.6(2)");

            begin
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
         end if;
      end Check_Hidden_State_Variables_And_Missing_Part_Of;

      ---------------------------
      -- Traverse_Declarations --
      ---------------------------

      procedure Traverse_Declarations (L : List_Id) is
         N : Node_Id := First (L);
      begin
         while Present (N) loop
            case Nkind (N) is
               when N_Object_Declaration =>
                  declare
                     E : constant Entity_Id := Defining_Entity (N);

                  begin
                     if ((Ekind (E) = E_Constant
                          and then Has_Variable_Input (E))
                         or else Ekind (E) = E_Variable)
                       and then not Is_Internal (E)
                       and then not Is_Part_Of_Concurrent_Object (E)
                     then
                        --  Detect which of the state variables are hidden or
                        --  are missing a Part_Of indicator and emit a message.
                        Check_Hidden_State_Variables_And_Missing_Part_Of (E);
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
                        Traverse_Declarations
                          (Visible_Declarations (Pkg_Spec));

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
      --  If the analyzed package has abstract states then traverse its private
      --  and body declarations.
      if Present (Abstract_States (FA.Spec_Entity))
        and then Private_Spec_In_SPARK (FA.Spec_Entity)
      then
         Traverse_Declarations (Private_Declarations (Pkg_Spec));

         if Entity_Body_In_SPARK (FA.Spec_Entity) then
            Traverse_Declarations (Declarations (Pkg_Body));
         end if;
      end if;

      --  Traverse declarations from the visible part of a private child.
      --  This is to enforce SPARK RM 7.2.6(3).
      if Is_Child_Unit (FA.Spec_Entity)
        and then Is_Private_Descendant (FA.Spec_Entity)
      then
         Traverse_Declarations (Visible_Declarations (Pkg_Spec));
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
      --  Returns True iff E is its declaration says it is initialized

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

                  for Write of Globals.Writes loop
                     --  ??? we should only care about abstract states of the
                     --  package that we are analyzing.
                     if Is_Abstract_State (Write)
                       and then not
                         Globals.Reads.Contains
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
        (Is_Null_State (E)
           or else
         (Has_Volatile (E)
            and then Has_Volatile_Flavor (E, Pragma_Async_Writers)));

   --  Start of processing for Find_Impossible_To_Initialize_State

   begin
      Collect_Procedure_Outputs;

      --  Issue error for every non-null abstract state that does not have
      --  Async_Writers, is not mentioned in an Initializes aspect and is not
      --  a pure output of any externally visible procedure.

      for State of Iter (Abstract_States (FA.Spec_Entity)) loop
         if not Trivially_Initialized (State)
           and then not Initialized_By_Initializes (Direct_Mapping_Id (State))
           and then not Outputs_Of_Procs.Contains (Direct_Mapping_Id (State))
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

   end Find_Impossible_To_Initialize_State;

   ----------------------------
   -- Check_Depends_Contract --
   ----------------------------

   procedure Check_Depends_Contract (FA : in out Flow_Analysis_Graphs) is

      User_Deps           : Dependency_Maps.Map;
      Projected_User_Deps : Dependency_Maps.Map;
      Actual_Deps         : Dependency_Maps.Map;

      Params         : Node_Sets.Set;
      Implicit_Param : Entity_Id;
      --  This set will hold all local parameters of the subprogram

      Depends_Scope : constant Flow_Scope :=
        (if Present (FA.Refined_Depends_N) then
            FA.B_Scope
         else
            FA.S_Scope);
      --  This is body scope if we are checking a Refined_Depends contract or
      --  spec scope if we are checking a Depends contract.

      function Message_Kind (F : Flow_Id) return Msg_Severity;
      --  Returns the severity of the message that we have to emit
      --
      --  In the absence of a user-provided Global contract the user-provided
      --  Depends contract is used to synthesize the Globals. In this case and
      --  if F is a global variable the emitted messages are errors since
      --  subprogram callers will be assuming wrong Globals.
      --
      --  On the other hand, when there is a user-provided Global contract or
      --  when F is not a Global variable, emitted messages are medium checks.

      ------------------
      -- Message_Kind --
      ------------------

      function Message_Kind (F : Flow_Id) return Msg_Severity is
      begin
         if No (FA.Global_N)
           and then F.Kind = Direct_Mapping
           and then not Params.Contains (Get_Direct_Mapping_Id (F))
         then
            return Error_Kind;
         end if;

         --  No need to raise an error
         return Medium_Check_Kind;
      end Message_Kind;

   --  Start of processing for Check_Depends_Contract

   begin
      if No (FA.Depends_N) then
         --  If the user has not specified a dependency relation we have no
         --  work to do.
         return;
      end if;

      Get_Depends (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Depends    => User_Deps);

      --  Populate the Params and Implicit_Param
      Params := Get_Formals (FA.Analyzed_Entity);
      Implicit_Param := Get_Implicit_Formal (FA.Analyzed_Entity);

      --  Up-project the dependencies
      Up_Project (User_Deps, Projected_User_Deps, Depends_Scope);
      Up_Project (FA.Dependency_Map, Actual_Deps, Depends_Scope);

      if Debug_Trace_Depends then
         Print_Dependency_Map ("user",   Projected_User_Deps);
         Print_Dependency_Map ("actual", Actual_Deps);
      end if;

      --  If the user depends do not include something we have in the actual
      --  depends we will raise an appropriate error. We should however also
      --  sanity check there is nothing in the user dependencies which is *not*
      --  in the actual dependencies.

      for C in Projected_User_Deps.Iterate loop
         declare
            F_Out : Flow_Id renames Dependency_Maps.Key (C);
         begin
            if not Actual_Deps.Contains (F_Out) then
               --  ??? check quotation in errout.ads
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "incorrect dependency & is not an output of &",
                  N        => Search_Contract (FA.Analyzed_Entity,
                                               Pragma_Depends,
                                               Get_Direct_Mapping_Id (F_Out)),
                  F1       => F_Out,
                  F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag      => Depends_Null,
                  Severity => Medium_Check_Kind);
            end if;
         end;
      end loop;

      --  We go through the actual dependencies because they are always
      --  complete.

      for C in Actual_Deps.Iterate loop
         declare
            F_Out  : Flow_Id          renames Dependency_Maps.Key (C);
            A_Deps : Flow_Id_Sets.Set renames Actual_Deps (C);
            U_Deps : Flow_Id_Sets.Set;

            Missing_Deps : Ordered_Flow_Id_Sets.Set;
            Wrong_Deps   : Ordered_Flow_Id_Sets.Set;

            Proceed_With_Analysis : Boolean := True;
         begin
            if F_Out = Null_Flow_Id then
               --  The null dependency is special: it may not be present in the
               --  user dependency because null => null would be super tedious
               --  to write.
               declare
                  Null_Dep : constant Dependency_Maps.Cursor :=
                    Projected_User_Deps.Find (Null_Flow_Id);
               begin
                  if Dependency_Maps.Has_Element (Null_Dep) then
                     --  ??? Move should be fine here
                     U_Deps := Projected_User_Deps (Null_Dep);
                  end if;
               end;
            elsif Projected_User_Deps.Contains (F_Out) then
               --  ??? repeated search in map
               U_Deps := Projected_User_Deps (F_Out);
            elsif F_Out.Kind = Magic_String then
               Global_Required (FA, F_Out);
               Proceed_With_Analysis := False;
            else
               --  If the Depends aspect is used to synthesize the Global
               --  aspect, then this message will be an error instead of a
               --  medium check.
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "expected to see & on the left-hand-side of" &
                              " a dependency relation",
                  N        => FA.Depends_N,
                  F1       => F_Out,
                  Tag      => Depends_Missing_Clause,
                  Severity => Message_Kind (F_Out));
            end if;

            --  If we mention magic strings anywhere, there is no point in
            --  proceeding as the dependency relation *cannot* be correct.

            if Proceed_With_Analysis then
               for Var of A_Deps loop
                  if Var.Kind = Magic_String then
                     Global_Required (FA, Var);
                     Proceed_With_Analysis := False;
                  end if;
               end loop;
            end if;

            --  If all is still well we now do a consistency check

            if Proceed_With_Analysis then
               Missing_Deps := To_Ordered_Flow_Id_Set (A_Deps - U_Deps);
               Wrong_Deps   := To_Ordered_Flow_Id_Set (U_Deps - A_Deps);

               for Missing_Var of Missing_Deps loop
                  declare
                     V : constant Flow_Graphs.Vertex_Id :=
                       Get_Initial_Vertex (FA.PDG, Missing_Var);
                  begin
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.Atr (V).Mode = Mode_Proof
                     then
                        null;
                     elsif F_Out = Null_Flow_Id
                       and then Missing_Var.Kind = Direct_Mapping
                       and then Present (Implicit_Param)
                       and then Implicit_Param =
                                  Get_Direct_Mapping_Id (Missing_Var)
                     then
                        --  Suppress missing dependencies related to implicit
                        --  concurrent objects.
                        null;
                     else
                        --  Something that the user dependency fails to
                        --  mention.
                        if not Is_Variable (Missing_Var) then
                           --  Dealing with a constant
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "& cannot appear in Depends",
                              N        => FA.Depends_N,
                              F1       => Missing_Var,
                              Tag      => Depends_Null,
                              Severity => Medium_Check_Kind);
                        elsif F_Out = Null_Flow_Id then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "missing dependency ""null => %""",
                              N        => FA.Depends_N,
                              F1       => Missing_Var,
                              Tag      => Depends_Null,
                              Severity => Medium_Check_Kind);
                        elsif F_Out = Direct_Mapping_Id
                          (FA.Analyzed_Entity)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      =>
                                "missing dependency ""%'Result => %""",
                              N        => Search_Contract
                                            (FA.Analyzed_Entity,
                                             Pragma_Depends,
                                             Get_Direct_Mapping_Id (F_Out)),
                              F1       => F_Out,
                              F2       => Missing_Var,
                              Tag      => Depends_Missing,
                              Severity => Medium_Check_Kind);
                        else
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "missing dependency ""% => %""",
                              N        => Search_Contract
                                            (FA.Analyzed_Entity,
                                             Pragma_Depends,
                                             Get_Direct_Mapping_Id (F_Out)),
                              F1       => F_Out,
                              F2       => Missing_Var,
                              Tag      => Depends_Missing,
                              Severity => Medium_Check_Kind);
                           --  ??? show path
                        end if;
                     end if;
                  end;
               end loop;

               for Wrong_Var of Wrong_Deps loop
                  --  Something the user dependency claims, but does not happen
                  --  in reality.
                  if Is_Abstract_State (Wrong_Var)
                    and then Wrong_Var.Kind in Direct_Mapping | Record_Field
                    and then State_Refinement_Is_Visible (Wrong_Var,
                                                          FA.B_Scope)
                    and then Has_Null_Refinement
                               (Get_Direct_Mapping_Id (Wrong_Var))
                  then
                     --  If the depends contract mentions a state with visible
                     --  null refinement then we do not need to emit a message
                     --  since this is trivially True.
                     null;
                  elsif F_Out.Kind = Direct_Mapping
                    and then Present (Implicit_Param)
                    and then Implicit_Param =
                               Get_Direct_Mapping_Id (Wrong_Var)
                    and then Wrong_Var.Kind = Direct_Mapping
                  then
                     --  Suppress incorrect dependencies related to implicit
                     --  concurrent objects.
                     null;
                  elsif not Is_Variable (Wrong_Var) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& cannot appear in Depends",
                        N        => FA.Depends_N,
                        F1       => Wrong_Var,
                        Tag      => Depends_Wrong,
                        Severity => Medium_Check_Kind);
                  elsif F_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "incorrect dependency ""null => %""",
                        N        => FA.Depends_N,
                        F1       => Wrong_Var,
                        Tag      => Depends_Wrong,
                        Severity => Medium_Check_Kind);
                     --  ??? show a path?
                  elsif F_Out = Direct_Mapping_Id (FA.Analyzed_Entity)
                    and then Ekind (FA.Analyzed_Entity) = E_Function
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "incorrect dependency ""%'Result => %""",
                        N        => Search_Contract
                                      (FA.Analyzed_Entity,
                                       Pragma_Depends,
                                       Get_Direct_Mapping_Id (F_Out),
                                       Get_Direct_Mapping_Id (Wrong_Var)),
                        F1       => F_Out,
                        F2       => Wrong_Var,
                        Tag      => Depends_Wrong,
                        Severity => Medium_Check_Kind);
                  else
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "incorrect dependency ""% => %""",
                        N        => Search_Contract
                                      (FA.Analyzed_Entity,
                                       Pragma_Depends,
                                       Get_Direct_Mapping_Id (F_Out),
                                       Get_Direct_Mapping_Id (Wrong_Var)),
                        F1       => F_Out,
                        F2       => Wrong_Var,
                        Tag      => Depends_Wrong,
                        Severity => Medium_Check_Kind);
                  end if;
               end loop;
            end if;
         end;
      end loop;
   end Check_Depends_Contract;

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
                        Msg      => "Refinement of % shall mention %",
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

      function Node_Id_Set_To_Flow_Id_Set
        (NS : Node_Sets.Set)
         return Flow_Id_Sets.Set;
      --  Takes a set of Node_Ids and returns a set of the
      --  corresponding Flow_Ids.

      function Flow_Id_Set_To_Vertex_Set
        (FS : Flow_Id_Sets.Set)
         return Vertex_Sets.Set;
      --  Takes a set of Flow_Ids and returns a set of PDG Vertices
      --  that correspond to these Flow_Ids after having changed
      --  their variants to Final_Value.

      procedure Write_Tracefile
        (From      : Flow_Graphs.Vertex_Id;
         To        : Vertex_Sets.Set;
         Tracefile : String);
      --  This procedure finds the shortest path connecting vertex
      --  From and any vertex contained in To. It then writes a
      --  tracefile containing all vertices in between (From
      --  and To excluded).

      --------------------------------
      -- Node_Id_Set_To_Flow_Id_Set --
      --------------------------------

      function Node_Id_Set_To_Flow_Id_Set
        (NS : Node_Sets.Set)
         return Flow_Id_Sets.Set
      is
         Tmp : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin
         for N of NS loop
            Tmp.Insert (Direct_Mapping_Id (N));
         end loop;

         return Tmp;
      end Node_Id_Set_To_Flow_Id_Set;

      -------------------------------
      -- Flow_Id_Set_To_Vertex_Set --
      -------------------------------

      function Flow_Id_Set_To_Vertex_Set
        (FS : Flow_Id_Sets.Set)
         return Vertex_Sets.Set
      is
         Tmp : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      begin
         for F of FS loop
            Tmp.Insert (Get_Final_Vertex (FA.PDG, F));
         end loop;

         return Tmp;
      end Flow_Id_Set_To_Vertex_Set;

      ---------------------
      -- Write_Tracefile --
      ---------------------

      procedure Write_Tracefile
        (From      : Flow_Graphs.Vertex_Id;
         To        : Vertex_Sets.Set;
         Tracefile : String)
      is
         Path_Found : Boolean := False;
         Path       : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

         procedure Are_We_There_Yet
           (V           : Flow_Graphs.Vertex_Id;
            Instruction : out Flow_Graphs.Traversal_Instruction);
         --  Visitor procedure for Shortest_Path.

         procedure Add_Loc (V : Flow_Graphs.Vertex_Id);
         --  Step procedure for Shortest_Path.

         ----------------------
         -- Are_We_There_Yet --
         ----------------------

         procedure Are_We_There_Yet
           (V           : Flow_Graphs.Vertex_Id;
            Instruction : out Flow_Graphs.Traversal_Instruction)
         is
         begin
            if To.Contains (V) then
               Instruction := Flow_Graphs.Found_Destination;
               Path_Found  := True;
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
            if not To.Contains (V)
              and then F.Kind = Direct_Mapping
            then
               Path.Include (V);
            end if;
         end Add_Loc;

      --  Start of processing for Write_Tracefile

      begin
         FA.PDG.Shortest_Path
           (Start         => From,
            Allow_Trivial => False,
            Search        => Are_We_There_Yet'Access,
            Step          => Add_Loc'Access);

         --  A little sanity check can't hurt.
         pragma Assert (Path_Found);

         Write_Vertex_Set
           (FA       => FA,
            Set      => Path,
            Filename => Tracefile);
      end Write_Tracefile;

      DM : constant Dependency_Maps.Map :=
        Parse_Initializes (FA.Spec_Entity,
                           Null_Flow_Scope);

   --  Start of processing for Check_Initializes_Contract

   begin
      --  We have nothing to do if DM is empty
      if DM.Is_Empty then
         return;
      end if;

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
                                        then Search_Contract
                                          (FA.Spec_Entity,
                                           Pragma_Initializes,
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

            --  If a variable or state abstraction that has not been
            --  mentioned in an Initializes aspect was found in the RHS of
            --  an initialization_item then we don't do any further analysis.
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

            All_Contract_Outs : Flow_Id_Sets.Set;
            All_Contract_Ins  : Flow_Id_Sets.Set;
            All_Actual_Ins    : Flow_Id_Sets.Set;
         begin
            --  Down project the LHS of an initialization_item
            All_Contract_Outs :=
              Node_Id_Set_To_Flow_Id_Set
                (Down_Project
                   (Var => Get_Direct_Mapping_Id (The_Out),
                    S   => FA.B_Scope));

            --  Down project the RHS of an initialization_item
            for G of The_Ins loop
               All_Contract_Ins.Union
                 (Node_Id_Set_To_Flow_Id_Set
                    (Down_Project
                       (Get_Direct_Mapping_Id (G), FA.B_Scope)));
            end loop;

            --  Populate All_Actual_Outs and All_Actual_Ins
            for O in FA.Dependency_Map.Iterate loop
               declare
                  Actual_Out : Flow_Id renames Dependency_Maps.Key (O);
                  Actual_Ins : Flow_Id_Sets.Set renames FA.Dependency_Map (O);
               begin
                  if All_Contract_Outs.Contains (Actual_Out) then
                     All_Actual_Ins.Union (Actual_Ins);
                  end if;
               end;
            end loop;

            --  Complain about actual inputs that are not mentioned in the
            --  Initializes.
            for Actual_In of All_Actual_Ins loop
               if not All_Contract_Ins.Contains (Actual_In) then
                  declare
                     Tracefile : constant String := Fresh_Trace_File;
                  begin
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       =>
                          "initialization of % must not depend on %",
                        SRM_Ref   => "7.1.5(11)",
                        N         => Search_Contract
                                       (FA.Spec_Entity,
                                        Pragma_Initializes,
                                        Get_Direct_Mapping_Id (The_Out)),
                        F1        => The_Out,
                        F2        => Actual_In,
                        Tag       => Initializes_Wrong,
                        Severity  => Medium_Check_Kind);

                     --  Generate and write the tracefile
                     Write_Tracefile
                       (From      => Get_Initial_Vertex (FA.PDG, Actual_In),
                        To        =>
                          Flow_Id_Set_To_Vertex_Set (All_Contract_Outs),
                        Tracefile => Tracefile);
                  end;
               end if;
            end loop;

            --  Complain about inputs mentioned in the Initializes that are not
            --  actual inputs.
            for Contract_In of All_Contract_Ins loop
               if not All_Actual_Ins.Contains (Contract_In) then
                  if Is_Variable (Contract_In) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "initialization of & does not depend on &",
                        SRM_Ref  => "7.1.5(11)",
                        N        => Search_Contract
                                      (FA.Spec_Entity,
                                       Pragma_Initializes,
                                       Get_Direct_Mapping_Id (The_Out)),
                        F1       => The_Out,
                        F2       => Contract_In,
                        Tag      => Initializes_Wrong,
                        Severity => Medium_Check_Kind);
                  else
                     --  The input is a constant without variable input
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& cannot appear in Initializes",
                        N        => Search_Contract
                                      (FA.Spec_Entity,
                                       Pragma_Initializes,
                                       Get_Direct_Mapping_Id (The_Out),
                                       Get_Direct_Mapping_Id (Contract_In)),
                        F1       => Contract_In,
                        Tag      => Initializes_Wrong,
                        Severity => Medium_Check_Kind);
                  end if;
               end if;
            end loop;

            --  Complain about outputs that are constants and should
            --  consequently not be mentioned in an initializes aspect.
            for Contract_Out of All_Contract_Outs loop
               if not Is_Variable (Contract_Out) then
                  --  Output is a constant without variable input
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& cannot appear in Initializes",
                     N        => Search_Contract
                                   (FA.Spec_Entity,
                                    Pragma_Initializes,
                                    Get_Direct_Mapping_Id (Contract_Out)),
                     F1       => Contract_Out,
                     Tag      => Initializes_Wrong,
                     Severity => Medium_Check_Kind);
               end if;
            end loop;
         end;
      end loop;
   end Check_Initializes_Contract;

   ----------------------------------
   -- Check_Refined_State_Contract --
   ----------------------------------

   procedure Check_Refined_State_Contract (FA : in out Flow_Analysis_Graphs) is
      Refined_State_N : constant Node_Id := Get_Pragma (FA.Analyzed_Entity,
                                                        Pragma_Refined_State);

   begin
      if Present (Refined_State_N) then
         declare
            DM : constant Dependency_Maps.Map :=
              Parse_Refined_State (Refined_State_N);

         begin
            for Constituents of DM loop
               for Constituent of Constituents loop
                  declare
                     Constituent_E : constant Entity_Id :=
                       Get_Direct_Mapping_Id (Constituent);

                  begin
                     if Ekind (Constituent_E) = E_Constant
                       and then not Has_Variable_Input (Constituent_E)
                     then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& cannot appear in Refined_State",
                           N        => Refined_State_N,
                           F1       => Constituent,
                           SRM_Ref  => "7.2.2(16)",
                           Tag      => Refined_State_Wrong,
                           Severity => Medium_Check_Kind);
                     end if;
                  end;
               end loop;
            end loop;
         end;
      end if;
   end Check_Refined_State_Contract;

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
         Vars : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Get_Attribute_Id (Attribute_Name (N)) = Attribute_Old
         then
            Vars := Get_Variables
              (N,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => True);

            for Var of Vars loop
               declare
                  Initial_V : constant Flow_Graphs.Vertex_Id :=
                    Get_Initial_Vertex (FA.CFG, Var);

               begin
                  if not FA.Atr (Initial_V).Is_Import then
                     Error_Msg_Flow
                       (FA         => FA,
                        Msg        => "& is not initialized at " &
                                      "subprogram entry",
                        Severity   => High_Check_Kind,
                        N          => First_Variable_Use
                                        (N        => N,
                                         FA       => FA,
                                         Scope    => FA.B_Scope,
                                         Var      => Var,
                                         Precise  => False,
                                         Targeted => False),
                        F1         => Var,
                        Tag        => Uninitialized);
                  end if;
               end;
            end loop;
         end if;

         return OK;
      end Check_Prefix;

      procedure Check_Prefix_Of_Tick_Old is new
        Traverse_Proc (Process => Check_Prefix);

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
   begin
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : V_Attributes renames FA.Atr (V);
         begin
            if Atr.Is_Program_Node
              and not Atr.Is_Exceptional_Path
              and Atr.Is_Callsite
            then
               Antialiasing.Check_Procedure_Call
                 (FA => FA,
                  N  => Get_Direct_Mapping_Id (FA.CFG.Get_Key (V)));
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

      function In_Body_Part (S : Flow_Scope) return Boolean
      with Pre => S /= Null_Flow_Scope;
      --  @param S is the Flow_Scope of the Constant_After_Elaboration variable
      --  @return True iff the Analyzed_Entity is defined in the body of the
      --     package that introduces the Constant_After_Elaboration variable.

      ------------------
      -- In_Body_Part --
      ------------------

      function In_Body_Part (S : Flow_Scope) return Boolean is
         Body_S : constant Flow_Scope := Body_Scope (S);
      begin
         --  We check if Body_S is visible from FA.S_Scope
         return Is_Visible (Body_S, FA.S_Scope);
      end In_Body_Part;

   --  Start of processing for Check_Constant_After_Elaboration

   begin
      if Ekind (FA.Analyzed_Entity) = E_Function then
         --  Skip this check when dealing with a function.
         return;
      end if;

      --  Check that the procedure/entry/task does not modify variables that
      --  have Constant_After_Elaboration set.
      declare
         Globals : Global_Flow_Ids;

         G_Out     : Entity_Id;
         CAE_Scope : Flow_Scope;
      begin
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Globals    => Globals);

         for W of Globals.Writes loop
            if W.Kind in Direct_Mapping | Record_Field then
               G_Out     := Get_Direct_Mapping_Id (W);
               CAE_Scope := Get_Flow_Scope (G_Out);

               if CAE_Scope /= Null_Flow_Scope
                 and then not In_Body_Part (CAE_Scope)
                 and then Ekind (G_Out) = E_Variable
                 and then Is_Constant_After_Elaboration (G_Out)
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "constant after elaboration & " &
                                 "must not be an output of procedure &",
                     Severity => High_Check_Kind,
                     N        => FA.Analyzed_Entity,
                     F1       => W,
                     F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag      => Not_Constant_After_Elaboration);
               end if;
            end if;
         end loop;
      end;
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
            if Is_Volatile (Change_Variant (F, Normal_Use)) then
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
         Check_Set_For_Volatiles (Globals.Reads);
         pragma Assert (Globals.Writes.Is_Empty);
      end;

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

                     Report_Violations (Object     => Object,
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
               use Name_Nat;

               Number_Of_Accesses : Nat := 0;
               --  Counts the number of accesses to the current entry object

               Current_Entry : Entity_Name renames
                 Name_To_Name_Lists.Key (Obj);
               --  Entry under analysis

               Max_Queue_Length : constant Nat :=
                 Max_Queue_Length_Map (Current_Entry);
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

      function Variable_Has_CAE (F : Flow_Id) return Boolean;
      --  Returns True iff F does not have Constant_After_Elaboration set.

      ----------------------
      -- Variable_Has_CAE --
      ----------------------

      function Variable_Has_CAE (F : Flow_Id) return Boolean is
      begin
         if F.Kind in Direct_Mapping | Record_Field then
            declare
               E : constant Entity_Id := Get_Direct_Mapping_Id (F);
            begin
               return Ekind (E) = E_Variable
                 and then Is_Constant_After_Elaboration (E);
            end;

         else
            return False;
         end if;
      end Variable_Has_CAE;

   --  Start of processing for Check_CAE_In_Preconditions

   begin
      --  We only perform this check on protected operations
      if Ekind (Scope (FA.Analyzed_Entity)) /= E_Protected_Type then
         return;
      end if;

      Preconditions := Get_Precondition_Expressions (FA.Analyzed_Entity);

      --  Populate global sets
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.S_Scope,
                   Classwide  => False,
                   Globals    => Globals);

      --  Add Proof_Ins to Reads
      Globals.Reads.Union (Globals.Proof_Ins);

      for Precondition of Preconditions loop
         declare
            VU : constant Flow_Id_Sets.Set :=
              Get_Variables (Precondition,
                             Scope                => FA.S_Scope,
                             Local_Constants      => FA.Local_Constants,
                             Fold_Functions       => False,
                             Use_Computed_Globals => True);
            --  The above set contains all variables used in the precondition.
         begin
            for Var of VU loop
               if Globals.Reads.Contains (Change_Variant (Var, In_View))
                 and then not Variable_Has_CAE (Var)
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
      --  Emit a high check for all publically visible variables modified
      --  at this vertex.

      -------------
      -- Visitor --
      -------------

      procedure Visitor (V  :     Vertex_Id;
                         TV : out Simple_Traversal_Instruction)
      is
         K : Flow_Id renames FA.PDG.Get_Key (V);

      begin
         TV := Continue;

         --  Only check nodes in the body
         if Present (K)
           and then K.Kind in Direct_Mapping | Record_Field
           and then Get_Flow_Scope (K.Node).Part = Body_Part
         then
            for Var of Visible_Vars loop
               if FA.Atr (V).Variables_Defined.Contains (Var) then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "modification of & in elaboration " &
                                 "requires Elaborate_Body on package &",
                     Severity => High_Check_Kind,
                     N        => Error_Location (FA.PDG, FA.Atr, V),
                     F1       => Var,
                     F2       => Direct_Mapping_Id (FA.Spec_Entity),
                     Tag      => Pragma_Elaborate_Body_Needed,
                     Vertex   => V);
               end if;
            end loop;
         end if;
      end Visitor;

   --  Start of processing for Check_Elaborate_Body

   begin
      --  We only check variables that we claim to initialize (either
      --  because we said so or because flow thinks so), since otherwise
      --  their use will be flagged as a potentially uninitialized read.

      Visible_Vars := Flow_Id_Sets.Empty_Set;
      declare
         C : Flow_Id_Sets.Cursor := FA.Spec_Vars.First;
         --  Cursor for iteration over container that is a component of a
         --  discriminated record. Such components cannot be iterated with
         --  FOR loop.
      begin
         while Flow_Id_Sets.Has_Element (C) loop
            declare
               Var : Flow_Id renames FA.Spec_Vars (C);
               Obj : constant Entity_Id := Get_Direct_Mapping_Id (Var);
            begin
               --  Ignore loop variables, in parameters and constants that are
               --  part of our local context.
               if not Is_Constant_Object (Obj)
                 and then Is_Initialized_At_Elaboration (Obj, FA.S_Scope)
               then
                  Visible_Vars.Insert (Var);
               end if;
            end;
            Flow_Id_Sets.Next (C);
         end loop;
      end;

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
                            F1       => Direct_Mapping_Id (FA.Spec_Entity));
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
      for State of Iter (Abstract_States (FA.Spec_Entity)) loop
         for Flavor in Volatile_Pragma_Id loop

            --  We only check if the state *does not* have a certain aspect
            if not Has_Volatile (State)
              or else not Has_Volatile_Flavor (State, Flavor)
            then

               --  And for each aspect we do not have, we make sure all
               --  (non-null) constituents also do not have it.
               for Constituent of Iter (Refinement_Constituents (State)) loop
                  if Nkind (Constituent) /= N_Null
                    and then Has_Volatile (Constituent)
                    and then Has_Volatile_Flavor (Constituent, Flavor)
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& cannot be a constituent of & "
                          & "(which lacks volatile flavor "
                          & To_String (Flavor) & ")",
                        Severity => High_Check_Kind,
                        N        => Constituent,
                        F1       => Direct_Mapping_Id (Constituent),
                        F2       => Direct_Mapping_Id (State));
                  end if;
               end loop;

            end if;
         end loop;

      end loop;
   end Check_State_Volatility_Escalation;

end Flow.Analysis;
