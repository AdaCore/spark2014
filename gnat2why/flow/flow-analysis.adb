------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2016, Altran UK Limited                 --
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
with Errout;                      use Errout;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Opt;                         use Opt;
with Output;                      use Output;
with Sem_Aux;                     use Sem_Aux;
with Sem_Util;                    use Sem_Util;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with Stand;                       use Stand;

with Common_Iterators;            use Common_Iterators;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with VC_Kinds;                    use VC_Kinds;

with Flow.Analysis.Antialiasing;
with Flow.Analysis.Sanity;
with Flow_Debug;                     use Flow_Debug;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Error_Messages;            use Flow_Error_Messages;
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
   use type Node_Sets.Set;
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
               --  Checks if N refers to Target and sets Resut to N if that is
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
                     declare
                        Body_E : constant Entity_Id := Get_Body_Entity (S);
                     begin
                        if Present (Body_E) then
                           Traverse
                             (Get_Pragma (Body_E, Pragma_Refined_Global));
                           if Result /= S then
                              return Result;
                           end if;
                        end if;
                     end;

                     Traverse (Get_Pragma (S, Pragma_Global));

                  when others =>
                     --  ??? E_Generic_Package, E_Generic_Package?
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
         if Get_Variables (N,
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
               or Atr.Is_Precondition
               or Atr.Is_Postcondition) and
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

   function Is_Param_Of_Null_Subp_Of_Generic (E : Entity_Id)
                                              return Boolean
   is
      Subp : constant Entity_Id := Scope (E);
   begin
      return (Ekind (E) in Formal_Kind
                and then Ekind (Subp) in E_Procedure | E_Function
                and then Is_Generic_Actual_Subprogram (Subp)
                and then Null_Present (Subprogram_Specification (Subp)));
   end Is_Param_Of_Null_Subp_Of_Generic;

   ------------------
   -- Analyse_Main --
   ------------------

   procedure Analyse_Main (FA : in out Flow_Analysis_Graphs) is
      Proof_Reads : Flow_Id_Sets.Set;
      Reads       : Flow_Id_Sets.Set;
      Unused      : Flow_Id_Sets.Set;
   begin
      if not FA.Is_Main then
         --  Nothing to see here, move along.
         return;
      end if;

      --  We need to make sure all global inputs are initialized. This
      --  means the following needs to hold:
      --     Input   ->   State must be initialized
      --     In_Out  ->   State must be initialized
      --     Output  ->   Always OK
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Proof_Ins  => Proof_Reads,
                   Reads      => Reads,
                   Writes     => Unused);
      Reads := To_Entire_Variables (Reads or Proof_Reads);
      --  Note we never actually need writes in this analysis.

      declare
         Init_Msg : constant String :=
           "& might not be initialized " &
           (case FA.Kind is
               when Kind_Subprogram =>
                  "after elaboration of main program &",
               when Kind_Task =>
                  "before start of tasks of type &",
               when others =>
                  raise Program_Error);

      begin
         for R of Reads loop
            if not Is_Initialized_At_Elaboration (R, FA.B_Scope) then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => Init_Msg,
                  N        => Find_Global (FA.Analyzed_Entity, R),
                  F1       => R,
                  F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag      => Uninitialized,
                  Severity => Medium_Check_Kind);
            end if;
         end loop;
      end;
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
         Sanity.Check_Part_Of'Access);
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
               when Kind_Subprogram |
                    Kind_Task       => (if Refined
                                        then "Refined_Global"
                                        else "Global"),
               when others => "Initializes");

            SRM_Ref : constant String :=
              (case FA.Kind is
               when Kind_Subprogram   |
                    Kind_Task         => "6.1.4(13)",
               when Kind_Package      |
                    Kind_Package_Body => "7.1.5(12)");

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
                        Tmp_A, Tmp_B, Tmp_C : Flow_Id_Sets.Set;
                     begin
                        Get_Globals (Subprogram => FA.Spec_Entity,
                                     Scope      => FA.S_Scope,
                                     Classwide  => False,
                                     Proof_Ins  => Tmp_A,
                                     Reads      => Tmp_B,
                                     Writes     => Tmp_C);

                        for F of To_Entire_Variables (Tmp_A or Tmp_B or Tmp_C)
                        loop
                           Vars_Known.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;

                  when Kind_Package | Kind_Package_Body =>
                     Vars_Known := Flow_Id_Sets.Empty_Set;

                     for F of To_Entire_Variables (FA.Visible_Vars) loop
                        if F.Kind in Direct_Mapping | Record_Field then
                           Vars_Known.Union
                             (To_Flow_Id_Set
                                (Down_Project
                                   (Node_Sets.To_Set
                                      (Get_Direct_Mapping_Id (F)),
                                    FA.S_Scope)));
                        else
                           Vars_Known.Include (F);
                        end if;
                     end loop;

                  when Kind_Task =>
                     raise Program_Error;
               end case;
            end if;

            for Expr of Get_Postcondition_Expressions (FA.Spec_Entity,
                                                       Refined)
            loop
               case FA.Kind is
                  when Kind_Subprogram =>
                     Vars_Used := To_Entire_Variables
                       (Get_Variables
                          (Expr,
                           Scope                => Get_Flow_Scope (Expr),
                           Local_Constants      => FA.Local_Constants,
                           Fold_Functions       => False,
                           Reduced              => True,
                           Use_Computed_Globals => True));

                  when Kind_Task =>
                     --  Nothing to do - no pre or postconditions.
                     Vars_Used := Flow_Id_Sets.Empty_Set;

                  when others =>
                     Vars_Used := To_Entire_Variables
                       (Get_Variables
                          (Expr,
                           Scope                => Private_Scope
                                                     (Get_Flow_Scope (Expr)),
                           Local_Constants      => FA.Local_Constants,
                           Fold_Functions       => False,
                           Reduced              => True,
                           Use_Computed_Globals => True));
               end case;
               Vars_Used.Difference (Quantified_Variables (Expr));

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
                        F1       => Entire_Variable (Var),
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Severity => Error_Kind);
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
         EV : constant Flow_Id := Entire_Variable (F);
      begin
         return Ekind (Etype (Get_Direct_Mapping_Id (EV))) in Concurrent_Kind;
      end Is_Or_Belongs_To_Concurrent_Object;

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
              or else Atr.Is_Precondition
              or else Atr.Is_Postcondition
              or else Atr.Is_Proof;
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

      --  We now detect imports that do not contribute to at least one export
      --  and objects that are never used.

      pragma Assert (Considered_Imports.Is_Empty and then
                     Considered_Objects.Is_Empty and then
                     Used.Is_Empty               and then
                     Effective.Is_Empty);

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Var : Flow_Id      renames FA.PDG.Get_Key (V);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if Var.Variant = Initial_Value and then
              Var.Kind /= Synthetic_Null_Export
            then
               declare
                  Entire_Var : constant Flow_Id :=
                    Change_Variant (Entire_Variable (Var), Normal_Use);
                  --  The entire variable

                  Disuse_Allowed : constant Boolean :=
                    Is_Bound (Var) or else Is_Discriminant (Var);
                  --  If this is a bound variable or discriminant, we only
                  --  consider it if it is actually used. Its not an error to
                  --  not explicitly use it.

               begin
                  --  Using discriminants or bounds marks the entire variable
                  --  as used; not using them has no effect. However, this
                  --  only applies to out parameters; for in out parameters the
                  --  value of the entire variable itself has to be used and
                  --  uses of bounds and discriminants are completely ignored.

                  --  Determine ineffective imports

                  if not Disuse_Allowed or else Atr.Mode /= Mode_In_Out then

                     if Atr.Is_Initialized and Atr.Is_Import then
                        if not Disuse_Allowed then
                           Considered_Imports.Include (Entire_Var);
                        end if;

                        --  Check if we're ineffective or not. If not, we note
                        --  that we at least partially have used the entire
                        --  variable.

                        if FA.PDG.Non_Trivial_Path_Exists
                          (V, Is_Final_Use'Access)
                        then
                           if Disuse_Allowed then
                              Considered_Imports.Include (Entire_Var);
                           end if;
                           Effective.Include (Entire_Var);
                        end if;
                     end if;

                     --  Determine unused objects

                     if not Disuse_Allowed then
                        Considered_Objects.Include (Entire_Var);
                     end if;

                     if FA.PDG.Out_Neighbour_Count (V) = 1 then
                        declare
                           Final_V : constant Flow_Graphs.Vertex_Id :=
                             FA.PDG.Child (V);
                        begin
                           if FA.PDG.Get_Key (Final_V).Variant /= Final_Value
                             or else FA.PDG.In_Neighbour_Count (Final_V) > 1
                           then
                              if Disuse_Allowed then
                                 Considered_Objects.Include (Entire_Var);
                              end if;
                              Used.Include (Entire_Var);
                           end if;
                        end;
                     else
                        if Disuse_Allowed then
                           Considered_Objects.Include (Entire_Var);
                        end if;
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

      --  Now that we can issue error messages. We can't do it inline (i.e. on
      --  detection above) because we need to pay special attention to records
      --  and unconstrained arrays.

      --  First we issue warnings on unused objects

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
                     Error_Location : constant Entity_Id :=
                       Find_Global (FA.Analyzed_Entity, F);
                     --  We prefer the report the error on the subprogram, not
                     --  on the global.

                  begin
                     --  Issue a different errors for variables and constants
                     if Is_Variable (F) then
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "unused global &",
                           N        => Error_Location,
                           F1       => F,
                           Tag      => VC_Kinds.Unused,
                           Severity => Low_Check_Kind,
                           Vertex   => V);
                     else
                        Error_Msg_Flow
                          (FA       => FA,
                           Msg      => "& cannot appear in Globals",
                           N        => Error_Location,
                           F1       => F,
                           Tag      => VC_Kinds.Unused,
                           Severity => Medium_Check_Kind,
                           Vertex   => V);
                     end if;
                  end;
               end if;
            else
               --  We suppress this warning when we are dealing with a
               --  concurrent type or a component of a concurrent type. Also
               --  when the variable has been marked either as Unreferenced
               --  or Unmodified or Unused or if it is a formal parameter of a
               --  null subprogram of a generic unit.
               if F.Kind /= Direct_Mapping
                 or else (Ekind (Etype (Get_Direct_Mapping_Id (F)))
                            not in Concurrent_Kind
                          and then not Is_Concurrent_Comp_Or_Disc (F)
                          and then not
                            Has_Pragma_Un (Get_Direct_Mapping_Id (F))
                          and then not
                            Is_Param_Of_Null_Subp_Of_Generic
                              (Get_Direct_Mapping_Id (F)))
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "unused variable &",
                     N        => Error_Location (FA.PDG, FA.Atr, V),
                     F1       => F,
                     Tag      => VC_Kinds.Unused,
                     Severity => Warning_Kind);
               end if;
            end if;
         end;
      end loop;

      --  Finally, we issue warnings on ineffective imports. We exclude items
      --  which are suppressed by a null derives and which have previously
      --  been flagged as unused. In the loop below we further exclude objects
      --  that are marked by a pragma Unreferenced or a pragma Unmodified or a
      --  pragma Unused.

      Ineffective := Considered_Imports - (Effective or Suppressed or Unused);

      for F of Ineffective loop
         declare
            V   : constant Flow_Graphs.Vertex_Id :=
              Get_Initial_Vertex (FA.PDG, F);
            Atr : V_Attributes renames FA.Atr (V);

         begin
            if F.Kind in Direct_Mapping | Record_Field
              and then Has_Pragma_Un (Get_Direct_Mapping_Id (F))
            then
               --  This variable is marked with a pragma Unreferenced, pragma
               --  Unused or pragma Unmodified so we do not emit the warning
               --  here.
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
                            (Get_Direct_Mapping_Id (F),
                             Body_Scope (FA.B_Scope))
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
               --  concurrent type or a component of a concurrent type.
               if F.Kind /= Direct_Mapping
                 or else (Ekind (Etype (Get_Direct_Mapping_Id (F))) not in
                            Concurrent_Kind
                          and then not Is_Concurrent_Comp_Or_Disc (F))
               then
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
         V : Flow_Graphs.Vertex_Id);
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

         N     : constant Node_Id := (if F.Kind = Direct_Mapping
                                      then Get_Direct_Mapping_Id (F)
                                      else Empty);

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
                   Change_Variant (Entire_Variable (Key), Normal_Use) /= F
               then
                  V_Use := Neighbour;
                  V_Error_Location := FA.Atr (Neighbour).Error_Location;
                  exit;
               end if;
            end;
         end loop;

         if Present (N)
           and then V_Use /= Flow_Graphs.Null_Vertex
           and then Is_Compilation_Unit (Scope (N))
           and then Scope (N) not in FA.Analyzed_Entity | FA.Spec_Entity
         then
            declare
               Current_Unit : constant Node_Id :=
                 Enclosing_Comp_Unit_Node (FA.Spec_Entity);
               Other_Unit   : constant Node_Id :=
                 Enclosing_Comp_Unit_Node (Scope (N));

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
                     F3       => Direct_Mapping_Id (Scope (N)),
                     Severity => Error_Kind,
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
            Key : Flow_Id renames FA.PDG.Get_Key (V);
            F   : Flow_Id;
         begin
            if Key.Variant = Initial_Value
              and then Key.Kind /= Synthetic_Null_Export
            then

               --  Note the Flow_Id of the entire variable
               F := Change_Variant (Entire_Variable (Key), Normal_Use);

               if Is_Abstract_State (F) then
                  Check_If_From_Another_Non_Elaborated_CU (F, V);
               end if;
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
      --  mentioned in a pragma Unreferenced, Unused or Unreferenced.

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
            Tmp       : Flow_Id;
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

                 --  Suppression for vertices that relate to proof
                 not Atr.Is_Proof
               then
                  Mask := Find_Masking_Code (V);
                  N    := Error_Location (FA.PDG, FA.Atr, V);

                  if Atr.Is_Parameter or Atr.Is_Global_Parameter then
                     if Atr.Is_Parameter then
                        Tmp := Direct_Mapping_Id
                          (Skip_Any_Conversions
                             (Get_Direct_Mapping_Id (Atr.Parameter_Actual)));
                     else
                        Tmp := Atr.Parameter_Formal;
                     end if;

                     if Atr.Is_Parameter and then Key.Variant = In_View then
                        --  For in parameters we do not emit the ineffective
                        --  assignment error as it is a bit confusing.
                        null;

                     elsif Atr.Is_Global_Parameter and then
                       Atr.Parameter_Formal.Variant = In_View
                     then
                        --  Ditto for globals in views.
                        null;

                     elsif Atr.Is_Discr_Or_Bounds_Parameter or else
                       Is_Bound (Key)
                     then
                        --  These are not there by choice, so the user
                        --  can't do anything to fix those. If its really
                        --  unused the non-discriminated part will be
                        --  ineffective.
                        null;

                     elsif Is_Easily_Printable (Tmp) then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "unused assignment to &",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           F1        => Tmp,
                           Tag       => Tag,
                           Severity  => Warning_Kind,
                           Vertex    => V);

                     else
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "unused assignment",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           Tag       => Tag,
                           Severity  => Warning_Kind,
                           Vertex    => V);
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
                        Get_Name_String (Chars (Defining_Identifier (N)));
                        Adjust_Name_Case (Sloc (N));

                        if FA.Kind in Kind_Package | Kind_Package_Body
                          and then No (Find_In_Initializes
                                         (Defining_Identifier (N)))
                        then
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "initialization of " &
                                           Name_Buffer (1 .. Name_Len) &
                                           " is not mentioned in " &
                                           "Initializes contract",
                              N         => FA.Initializes_N,
                              Tag       => Tag,
                              Severity  => Warning_Kind,
                              Vertex    => V);
                        else
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "initialization of " &
                                           Name_Buffer (1 .. Name_Len) &
                                           " has no effect",
                              N         => Error_Location (FA.PDG, FA.Atr, V),
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

      function AS_In_Generated_Initializes (Var : Flow_Id) return Boolean;
      --  Check if Var is a constituent of an abstract state that is mentioned
      --  in a generated Initializes aspect.

      function Consider_Vertex (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Returns True iff V should be considered for uninitialized variables

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

      procedure Emit_Message (Var              : Flow_Id;
                              Vertex           : Flow_Graphs.Vertex_Id;
                              Is_Initialized   : Boolean;
                              Is_Uninitialized : Boolean)
      with Pre => Is_Initialized or Is_Uninitialized;
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

      ---------------------------------
      -- AS_In_Generated_Initializes --
      ---------------------------------

      function AS_In_Generated_Initializes (Var : Flow_Id)
        return Boolean is
        (FA.Kind in Kind_Package | Kind_Package_Body
            and then Is_Constituent (Var)
            and then Mentioned_On_Generated_Initializes
                       (Direct_Mapping_Id
                          (Encapsulating_State
                             (Get_Direct_Mapping_Id
                                (Var)))));

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
      -- Mentioned_On_Generated_Initialized --
      ----------------------------------------

      function Mentioned_On_Generated_Initializes
        (Var : Flow_Id)
         return Boolean
      is
         DM : constant Dependency_Maps.Map :=
           GG_Get_Initializes (FA.Spec_Entity, FA.S_Scope);

      begin
         return
           (for some Init_Var in DM.Iterate =>
              Dependency_Maps.Key (Init_Var) = Var);
      end Mentioned_On_Generated_Initializes;

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

      ------------------
      -- Emit_Message --
      ------------------

      procedure Emit_Message (Var              : Flow_Id;
                              Vertex           : Flow_Graphs.Vertex_Id;
                              Is_Initialized   : Boolean;
                              Is_Uninitialized : Boolean)
      is
         type Msg_Kind is (Init, Unknown, Err);

         V_Key        : Flow_Id renames FA.PDG.Get_Key (Vertex);

         V_Initial    : constant Flow_Graphs.Vertex_Id :=
           FA.PDG.Get_Vertex (Change_Variant (Var, Initial_Value));

         Kind         : Msg_Kind :=
           (if Is_Initialized and Is_Uninitialized then Unknown
            elsif Is_Initialized                   then Init
            else                                        Err);

         N            : Node_Or_Entity_Id := FA.Atr (Vertex).Error_Location;
         Msg          : Unbounded_String;

         V_Error      : Flow_Graphs.Vertex_Id;
         V_Goal       : Flow_Graphs.Vertex_Id;
         V_Allowed    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

         Is_Final_Use : constant Boolean := V_Key.Variant = Final_Value;
         Is_Global    : constant Boolean := FA.Atr (V_Initial).Is_Global;
         Default_Init : constant Boolean := Is_Default_Initialized (Var);

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

         Msg :=
           To_Unbounded_String
             ((case Kind is
                  when Init =>
                     "initialization of & proved",
                  when Unknown =>
                     (if Default_Init
                      then "input value of & might be used"
                      else "& might not be "),
                  when Err =>
                     (if Default_Init
                      then "input value of & will be used"
                      else "& is not ")));

         case Kind is
            when Unknown | Err =>
               if not Default_Init then
                  if Has_Async_Readers (Var) then
                     Append (Msg, "written");
                  else
                     Append (Msg, "initialized");
                  end if;
               end if;
               if Is_Final_Use and not Is_Global then
                  Append (Msg, " in &");
               end if;
            when others =>
               null;
         end case;

         if not Is_Final_Use then
            V_Goal    := V_Error;
            V_Allowed := Vertex;
            N         := First_Variable_Use
              (N        => Error_Location (FA.PDG, FA.Atr, V_Error),
               FA       => FA,
               Scope    => FA.B_Scope,
               Var      => Var,
               Precise  => True,
               Targeted => True);
         elsif Is_Global then
            V_Goal := FA.Helper_End_Vertex;
            N      := Find_Global (FA.Analyzed_Entity, Var);
         else
            V_Goal := V_Error;
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
      end Emit_Message;

   --  Start of processing for Find_Use_Of_Uninitialized_Variables

   begin
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
                  if (FA.Atr (Initial_Value_Of_Var_Used).Is_Initialized
                      and then not AS_In_Generated_Initializes (Var_Used))
                    or else
                      (FA.Kind in Kind_Package | Kind_Package_Body
                       and then
                         (Is_Abstract_State (Var_Used)
                          or else
                            (Final_Value_Of_Var_Used = V
                             and then
                               Mentioned_On_Generated_Initializes (Var_Used))))
                    or else
                      (Var_Used.Kind in Direct_Mapping | Record_Field
                       and then
                         Is_Constant_Object (Get_Direct_Mapping_Id (Var_Used)))
                  then
                     --  ... we either do nothing because it is safe, or...
                     null;

                  else
                     --  ... we check the in-neighbours in the DDG and see if
                     --  they define it. We record initialized / uninitialized
                     --  reads accordingly.
                     --
                     --  Note we skip this check for abstract state iff we
                     --  analyze a package, since it is OK to leave some state
                     --  uninitialized (Check_Initializes_Contract will pick
                     --  this up). We also skip this check when checking final
                     --  vertices of variables mentioned in the generated
                     --  Initializes aspect.
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
      M    : Attribute_Maps.Map := FA.Atr;
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
            if Present (Output)
              and then Output.Kind in Direct_Mapping | Record_Field
              and then not Is_Ghost_Entity (Get_Direct_Mapping_Id (Output))
            then
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
                              Severity  => Error_Kind,
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

      function Enclosing_Package_Has_State (E : Entity_Id) return Boolean;
      --  Returns True if there is an enclosing package of E (not
      --  necessarily direcly) which has a state abstraction.

      procedure Warn_About_Hidden_States (E : Entity_Id);
      --  Issues a medium check per hidden state found in package E

      procedure Warn_About_Unreferenced_Constants (E : Entity_Id);
      --  Issues a high check for every constant with variable input
      --  which is not exposed through a state abstraction.

      ---------------------------------
      -- Enclosing_Package_Has_State --
      ---------------------------------

      function Enclosing_Package_Has_State (E : Entity_Id) return Boolean is
         Scop : Entity_Id := E;
      begin
         loop
            --  If we find a package then we look if it has abstract state

            pragma Assert (Ekind (Scop) /= E_Generic_Package);

            if Ekind (Scop) = E_Package
              and then Present (Abstract_States (Scop))
            then
               return True;

            --  If we find a public child then we return False

            elsif Is_Child_Unit (Scop)
              and then not Is_Private_Descendant (Scop)
            then
               return False;

            end if;

            Scop := Scope (Scop);

            --  If we reach Standard_Standard then there is no enclosing
            --  package which has state.

            exit when Scop = Standard_Standard;
         end loop;

         return False;
      end Enclosing_Package_Has_State;

      ------------------------------
      -- Warn_About_Hidden_States --
      ------------------------------

      procedure Warn_About_Hidden_States (E : Entity_Id) is

         procedure Warn_On_Non_Constant (First_Ent : Entity_Id);
         --  Goes through a list of entities and issues medium checks
         --  for any non-constant variables.

         --------------------------
         -- Warn_On_Non_Constant --
         --------------------------

         procedure Warn_On_Non_Constant (First_Ent : Entity_Id) is
            Hidden_State : Entity_Id;
         begin
            Hidden_State := First_Ent;
            while Present (Hidden_State) loop
               if Ekind (Hidden_State) in Object_Kind
                 and then Is_Variable (Direct_Mapping_Id (Hidden_State))
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& needs to be a constituent of " &
                                   "some state abstraction",
                     N        => Hidden_State,
                     F1       => Direct_Mapping_Id (Hidden_State),
                     Tag      => Hidden_Unexposed_State,
                     Severity => Medium_Check_Kind);
               end if;

               Next_Entity (Hidden_State);
            end loop;
         end Warn_On_Non_Constant;

      --  Start of processing for Warn_About_Hidden_States

      begin
         --  Warn about hidden states that lie in the private part
         Warn_On_Non_Constant (First_Private_Entity (E));

         --  Warn about hidden states that lie in the body
         if Present (Body_Entity (E)) then
            Warn_On_Non_Constant (First_Entity (Body_Entity (E)));
         end if;
      end Warn_About_Hidden_States;

      ---------------------------------------
      -- Warn_About_Unreferenced_Constants --
      ---------------------------------------

      procedure Warn_About_Unreferenced_Constants (E : Entity_Id) is
         Refined_State_N  : constant Node_Id :=
           Get_Pragma (Body_Entity (E),
                       Pragma_Refined_State);

         DM               : Dependency_Maps.Map;
         All_Constituents : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         procedure Warn_On_Unexposed_Constant (First_Ent : Entity_Id);
         --  Goes through a list of entities and issues medium checks
         --  for any unexposed constants with variable inputs.

         --------------------------------
         -- Warn_On_Unexposed_Constant --
         --------------------------------

         procedure Warn_On_Unexposed_Constant (First_Ent : Entity_Id) is
            Hidden_State : Entity_Id;
            F            : Flow_Id;
         begin
            Hidden_State := First_Ent;
            while Present (Hidden_State) loop
               F := Direct_Mapping_Id (Hidden_State);

               if Ekind (Hidden_State) in Object_Kind
                 and then Is_Constant_Object (Hidden_State)
                 and then Has_Variable_Input (Hidden_State)
                 and then not All_Constituents.Contains (F)
               then
                  Error_Msg_Flow
                    (FA       => FA,
                     Msg      => "& needs to be a constituent of " &
                                   "some state abstraction",
                     N        => Hidden_State,
                     F1       => F,
                     Tag      => Hidden_Unexposed_State,
                     Severity => Medium_Check_Kind);
               end if;

               Next_Entity (Hidden_State);
            end loop;
         end Warn_On_Unexposed_Constant;

      --  Start of processing for Warn_About_Unreferenced_Constants

      begin
         --  Sanity check that we do have a Refined_State aspect
         pragma Assert (Present (Refined_State_N));

         --  Gather up all constituents mentioned in the Refined_State
         --  aspect.
         DM := Parse_Refined_State (Refined_State_N);
         for State of DM loop
            All_Constituents.Union (State);
         end loop;

         --  Warn about hidden unexposed constants with variable input
         --  that lie in the private part.
         Warn_On_Unexposed_Constant (First_Private_Entity (E));

         --  Warn about hidden unexposed constants with variable input
         --  that lie in the body.
         Warn_On_Unexposed_Constant (First_Entity (Body_Entity (E)));
      end Warn_About_Unreferenced_Constants;

   --  Start of processing for Find_Hidden_Unexposed_State

   begin
      if Present (Abstract_States (FA.Spec_Entity)) then
         --  If the package has an abstract state aspect then issue high
         --  checks for every constant with variable input that is part of
         --  the package's hidden state and is not exposed through a state
         --  abstraction.
         if Entity_Body_In_SPARK (FA.Spec_Entity) then
            Warn_About_Unreferenced_Constants (FA.Spec_Entity);
         end if;

      else
         --  If the package does not have an abstract state aspect and an
         --  enclosing package does introduces a state abstraction then issue
         --  a medium check per hidden state.

         if Enclosing_Package_Has_State (FA.Spec_Entity) then
            Warn_About_Hidden_States (FA.Spec_Entity);
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
        Parse_Initializes (FA.Initializes_N, FA.Spec_Entity, FA.S_Scope);

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
                  Proof_Ins : Flow_Id_Sets.Set;
                  Reads     : Flow_Id_Sets.Set;
                  Writes    : Flow_Id_Sets.Set;
               begin
                  Get_Globals (Subprogram => E,
                               Scope      => FA.S_Scope,
                               Classwide  => False,
                               Proof_Ins  => Proof_Ins,
                               Reads      => Reads,
                               Writes     => Writes);

                  --  If the Flow_Id is an Output (and not an Input) of the
                  --  procedure then include it in Outputs.

                  for Write of Writes loop
                     --  ??? we should only care about abstract states of the
                     --  package that we are analyzing.
                     if Is_Abstract_State (Write)
                       and then not
                         Reads.Contains (Change_Variant (Write, In_View))
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

      User_Deps   : Dependency_Maps.Map;
      Actual_Deps : Dependency_Maps.Map;

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

      function Up_Project_Map
        (DM : Dependency_Maps.Map)
         return Dependency_Maps.Map;
      --  Up projects the constituents that are mentioned in DM to their
      --  encapsulating state abstractions visible from Depends_Scope.
      --
      --  Example:
      --     State1 => (Con1, Con2)
      --     State2 => (Con3, Con4)
      --
      --     Original DM:
      --       Con1 => (Con3, G)
      --       Con3 => (Con4, G)
      --       G    => Con3
      --
      --     Up-projected DM:
      --       State1 => (State1, State2, G)
      --       State2 => (State2, G)
      --       G      => State2
      --
      --  Note that the self-depence of State1 is an indirect consequence of
      --  the fact that Con2 is not an Output. So there is an implicit Con2 =>
      --  Con2 dependence.

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

      --------------------
      -- Up_Project_Map --
      --------------------

      function Up_Project_Map
        (DM : Dependency_Maps.Map)
         return Dependency_Maps.Map
      is
         States_Written       : Node_Sets.Set;
         Constituents_Written : Node_Sets.Set;
         Up_Projected_Map     : Dependency_Maps.Map;

      begin
         for C in DM.Iterate loop
            declare
               F_Out  : Flow_Id          renames Dependency_Maps.Key (C);
               F_Deps : Flow_Id_Sets.Set renames DM (C);
               AS     : Flow_Id;

               Position : Dependency_Maps.Cursor;
               --  Position of the mapped dependent entity

               Unused : Boolean;
               --  Dummy variable required by the maps API

            begin
               --  Add output
               if Is_Non_Visible_Constituent (F_Out, Depends_Scope) then
                  AS := Up_Project_Constituent (F_Out, Depends_Scope);

                  --  Add the encapsulating abstract state to the map (if it is
                  --  not already there).
                  Up_Projected_Map.Insert (Key      => AS,
                                           Position => Position,
                                           Inserted => Unused);

                  --  Taking some notes
                  States_Written.Include (Get_Direct_Mapping_Id (AS));
                  Constituents_Written.Include (Get_Direct_Mapping_Id (F_Out));
               else
                  --  Add output as it is
                  Up_Projected_Map.Insert (Key      => F_Out,
                                           Position => Position,
                                           Inserted => Unused);
               end if;

               --  Add output's dependencies
               declare
                  Up_Projected_Deps : Flow_Id_Sets.Set renames
                    Up_Projected_Map (Position);
               begin
                  for Dep of F_Deps loop
                     Up_Projected_Deps.Include
                       (if Is_Non_Visible_Constituent (Dep, Depends_Scope)
                          then Up_Project_Constituent (Dep, Depends_Scope)
                          else Dep);
                  end loop;
               end;
            end;
         end loop;

         --  If at least one constituent of a state abstraction has not been
         --  written, then the state abstraction also depends on itself.
         for State of States_Written loop
            for RC of Iter (Refinement_Constituents (State)) loop
               if not Constituents_Written.Contains (RC) then
                  declare
                     AS : constant Flow_Id := Direct_Mapping_Id (State);
                  begin
                     --  Abstract state also depends on itself
                     Up_Projected_Map (AS).Include (AS);
                  end;

                  --  There is no need to check the rest of the constituents
                  exit;
               end if;
            end loop;
         end loop;

         return Up_Projected_Map;
      end Up_Project_Map;

   --  Start of processing for Check_Depends_Contract

   begin
      if No (FA.Depends_N) then
         --  If the user has not specified a dependency relation we have no
         --  work to do.
         return;
      end if;

      Get_Depends (Subprogram => FA.Analyzed_Entity,
                   Scope      => Depends_Scope,
                   Classwide  => False,
                   Depends    => User_Deps);

      --  Populate the Params and Implicit_Param
      Params := Get_Formals (FA.Analyzed_Entity);
      Implicit_Param := Get_Implicit_Formal (FA.Analyzed_Entity);

      --  Up-project the dependencies
      User_Deps   := Up_Project_Map (User_Deps);
      Actual_Deps := Up_Project_Map (FA.Dependency_Map);

      if Debug_Trace_Depends then
         Print_Dependency_Map (User_Deps);
         Print_Dependency_Map (Actual_Deps);
      end if;

      --  If the user depends do not include something we have in the actual
      --  depends we will raise an appropriate error. We should however also
      --  sanity check there is nothing in the user dependencies which is *not*
      --  in the actual dependencies.

      for C in User_Deps.Iterate loop
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
                    User_Deps.Find (Null_Flow_Id);
               begin
                  if Dependency_Maps.Has_Element (Null_Dep) then
                     --  ??? Move should be fine here
                     U_Deps := User_Deps (Null_Dep);
                  end if;
               end;
            elsif User_Deps.Contains (F_Out) then
               --  ??? repeated search in map
               U_Deps := User_Deps (F_Out);
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
                    and then State_Refinement_Is_Visible
                               (Get_Direct_Mapping_Id (Wrong_Var),
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
        and then Present (Abstract_States (FA.Spec_Entity))
      then
         for State of Iter (Abstract_States (FA.Spec_Entity)) loop
            declare
               Child_State   : constant Entity_Id := State;
               Encapsulating : constant Entity_Id :=
                 Encapsulating_State (State);

               Scop : constant Entity_Id := Scope (FA.Spec_Entity);

            begin
               if Present (Encapsulating)
                 and then Present (Scop)
                 and then Present (Abstract_States (Scop))
               then
                  for State of Iter (Abstract_States (Scop)) loop
                     if State /= Encapsulating then
                        exit;
                     else
                        if Refinement_Exists (State)
                          and then not Find_In_Refinement (State, Child_State)
                        then
                           Error_Msg_Flow
                             (FA       => FA,
                              Msg      => "Refinement of % shall mention %",
                              Severity => Error_Kind,
                              F1       => Direct_Mapping_Id (Encapsulating),
                              F2       => Direct_Mapping_Id (Child_State),
                                 N        => Scop,
                              SRM_Ref  => "7.2.6(6)");
                        end if;
                     end if;
                  end loop;
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
        Parse_Initializes (FA.Initializes_N,
                           FA.Spec_Entity,
                           Null_Flow_Scope);

   --  Start of processing for Check_Initializes_Contract

   begin
      --  We have nothing to do if DM is empty
      if DM.Is_Empty then
         return;
      end if;

      declare
         Found_Uninitialized : Boolean := False;
      begin
         --  If we are dealing with a library level package then we check if
         --  everything in the RHS of an initialization_item has been
         --  initialized.
         if Is_Library_Level_Entity (FA.Analyzed_Entity) then
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
         end if;

         --  If a variable or state abstraction that has not been mentioned in
         --  an Initializes aspect was found in the RHS of an
         --  initialization_item then we don't do any further analysis.
         if Found_Uninitialized then
            return;
         end if;
      end;

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
                   (Vars => Node_Sets.To_Set (Get_Direct_Mapping_Id (The_Out)),
                    S    => FA.B_Scope));

            --  Down project the RHS of an initialization_item
            for G of The_Ins loop
               All_Contract_Ins.Union
                 (Node_Id_Set_To_Flow_Id_Set
                    (Down_Project
                       (Vars => Node_Sets.To_Set (Get_Direct_Mapping_Id (G)),
                        S    => FA.B_Scope)));
            end loop;

            --  Populate the All_Actual_Outs and All_Actual_Ins sets
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

            --  Raise medium checks for actual inputs that are not mentioned by
            --  the Initializes.
            for Actual_In of All_Actual_Ins loop
               if not All_Contract_Ins.Contains (Actual_In)
                 and then not All_Contract_Outs.Contains (Actual_In)
               then
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

            --  Raise medium checks for inputs mentioned in the Initializes
            --  that are not actual inputs.
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

            --  Raise medium checks for outputs that are constants and should
            --  consequently not be mention in an initializes aspect.
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
         Proof_Ins : Flow_Id_Sets.Set;
         Reads     : Flow_Id_Sets.Set;
         Writes    : Flow_Id_Sets.Set;

         G_Out     : Entity_Id;
         CAE       : Node_Id;
         CAE_Scope : Flow_Scope;
      begin
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Proof_Ins  => Proof_Ins,
                      Reads      => Reads,
                      Writes     => Writes);

         for W of Writes loop
            if W.Kind in Direct_Mapping | Record_Field then
               G_Out     := Get_Direct_Mapping_Id (W);
               CAE_Scope := Get_Flow_Scope (G_Out);

               if CAE_Scope /= Null_Flow_Scope then
                  CAE := Empty;

                  if Ekind (G_Out) = E_Variable then
                     CAE := Get_Pragma (G_Out,
                                        Pragma_Constant_After_Elaboration);
                  end if;

                  if Is_Constant_After_Elaboration (CAE)
                    and then not In_Body_Part (CAE_Scope)
                  then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "constant after elaboration & must not" &
                                    " be an output of procedure &",
                        Severity => High_Check_Kind,
                        N        => FA.Analyzed_Entity,
                        F1       => W,
                        F2       => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag      => Not_Constant_After_Elaboration);
                  end if;
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
            if Is_Volatile (Change_Variant (F, Normal_Use), FA.B_Scope) then
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
      if Ekind (FA.Analyzed_Entity) not in E_Function | E_Generic_Function
      then
         --  If we are not dealing with a [generic] function then we have
         --  nothing to do here.
         return;
      end if;

      Volatile_Effect_Expected :=
        (if Is_Protected_Type (Scope (FA.Analyzed_Entity))
         then Is_Volatile_For_Internal_Calls (FA.Analyzed_Entity)
         else Is_Volatile_Function (FA.Analyzed_Entity));

      declare
         Proof_Ins : Flow_Id_Sets.Set;
         Reads     : Flow_Id_Sets.Set;
         Writes    : Flow_Id_Sets.Set;
      begin
         --  Populate global sets
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Proof_Ins  => Proof_Ins,
                      Reads      => Reads,
                      Writes     => Writes);

         --  Check globals for volatiles and emit messages if needed
         Check_Set_For_Volatiles (Proof_Ins or Reads or Writes);
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

      subtype Tasking_Owners_Kind is Tasking_Info_Kind
        range
        Suspends_On ..
        --  Entry_Calls
        Unsynch_Accesses;

      Concurrent_Object_Owner : array (Tasking_Owners_Kind) of Name_Maps.Map;
      --  Mapping from concurrent objects to a task instance that owns them,
      --  i.e. suspends on a suspension object or calls an entry. It stores
      --  only the first owning task instance, if there are more then it is
      --  SPARK violation.

      use Flow_Generated_Globals;

      procedure Check_Ownership (Task_Instance : Task_Object;
                                 Object        : Entity_Name;
                                 Owning_Kind   : Tasking_Owners_Kind);
      --  Check ownership of a kind Owning_Kind of the Object by a
      --  Task_Instance.

      ---------------------
      -- Check_Ownership --
      ---------------------

      procedure Check_Ownership (Task_Instance : Task_Object;
                                 Object        : Entity_Name;
                                 Owning_Kind   : Tasking_Owners_Kind)
      is
         use Name_Maps;

         Other_Task : constant Name_Maps.Cursor :=
           Concurrent_Object_Owner (Owning_Kind).Find (Object);
         --  Pointer to other task possibly accessing the object

         Dummy : Boolean;
         --  Dummy variable required by the Error_Msg_Flow API

         Msg : constant String :=
           (case Owning_Kind is
            when Suspends_On =>
                  "multiple tasks might suspend on suspension object &",
            when Entry_Calls =>
                  "multiple tasks might suspend on protected object &",
            when Unsynch_Accesses =>
                  "possible data race when accessing variable &");
         --  Main error message

         Severity : constant Check_Kind := High_Check_Kind;
         --  Severity of the error message

         SRM_Ref : constant String :=
           (if Owning_Kind in Suspends_On | Entry_Calls
            then "9(11)"
            else "");
         --  Reference to SPARK RM for non-obvious verification rules

         Msg_Attach_Node : constant Node_Id :=
           (if Present (Task_Instance.Node)
            then Task_Instance.Node
            else Defining_Entity (Unit (GNAT_Root)));
         --  Node for attaching the error message. It is preferably the node
         --  of a task instance. However, if the task is instantiated in the
         --  private part of a with-ed package and we have no the instance node
         --  then the best we can get is root node of the current compilation
         --  unit.

      begin
         --  There is a conflict if this object declares several tasks
         if Task_Instance.Instances = Many
           or else Has_Element (Other_Task)
         then
            Error_Msg_Flow
              (E            => Msg_Attach_Node,
               N            => Msg_Attach_Node,
               Suppressed   => Dummy,
               Severity     => Severity,
               Msg          => Msg,
               F1           => Magic_String_Id (Object),
               SRM_Ref      => SRM_Ref,
               Continuation => False);

            Error_Msg_Flow
              (E            => Msg_Attach_Node,
               N            => Msg_Attach_Node,
               Suppressed   => Dummy,
               Severity     => Severity,
               Msg          => "with task &",
               F1           => Magic_String_Id (Task_Instance.Name),
               Continuation => True);

            --  If an instance of another task type also accesses this object
            --  then point also to that task instance.
            if Has_Element (Other_Task) then
               Error_Msg_Flow
                 (E            => Msg_Attach_Node,
                  N            => Msg_Attach_Node,
                  Suppressed   => Dummy,
                  Severity     => Severity,
                  Msg          => "with task &",
                  F1           =>
                    Magic_String_Id (Name_Maps.Element (Other_Task)),
                  Continuation => True);
            end if;
         end if;

         if not Has_Element (Other_Task) then
            --  Otherwise just record this ownership
            Concurrent_Object_Owner
              (Owning_Kind).Insert (Object, Task_Instance.Name);
         end if;

      end Check_Ownership;

   --  Start of processing for Check_Concurrent_Accesses

   begin
      for C in Task_Instances.Iterate loop
         declare
            This_Task_Type : Entity_Name renames Task_Instances_Maps.Key (C);
            This_Task_Objects : Task_Lists.List renames Task_Instances (C);

         begin
            for This_Task_Object of This_Task_Objects loop
               for Owning_Kind in Tasking_Owners_Kind loop
                  for Obj of Tasking_Objects (Owning_Kind, This_Task_Type) loop
                     Check_Ownership (Task_Instance => This_Task_Object,
                                      Object        => Obj,
                                      Owning_Kind   => Owning_Kind);
                  end loop;
               end loop;
            end loop;
         end;
      end loop;

   end Check_Concurrent_Accesses;

   --------------------------------
   -- Check_CAE_In_Preconditions --
   --------------------------------

   procedure Check_CAE_In_Preconditions (FA : in out Flow_Analysis_Graphs) is

      Preconditions : Node_Lists.List;

      Reads         : Flow_Id_Sets.Set;
      Proof_Ins     : Flow_Id_Sets.Set;
      Unused        : Flow_Id_Sets.Set;
      --  The above 3 sets will contain the relevant globals.

      function Variable_Has_CAE (F : Flow_Id) return Boolean;
      --  Returns True iff F does not have Constant_After_Elaboration set.

      ----------------------
      -- Variable_Has_CAE --
      ----------------------

      function Variable_Has_CAE (F : Flow_Id) return Boolean is
      begin
         if F.Kind in Direct_Mapping | Record_Field then
            declare
               E   : constant Entity_Id := Get_Direct_Mapping_Id (F);
               CAE : constant Node_Id :=
                 (if Ekind (E) = E_Variable
                  then Get_Pragma (E, Pragma_Constant_After_Elaboration)
                  else Empty);
            begin
               return Is_Constant_After_Elaboration (CAE);
            end;

         else
            return False;
         end if;
      end Variable_Has_CAE;

   --  Start of processing for Check_CAE_In_Preconditions

   begin
      if not Belongs_To_Protected_Object
               (Direct_Mapping_Id (FA.Analyzed_Entity))
      then
         --  We only perform this check on protected operations.
         return;
      end if;

      Preconditions := Get_Precondition_Expressions (FA.Analyzed_Entity);

      --  Populate global sets
      Get_Globals (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.S_Scope,
                   Classwide  => False,
                   Proof_Ins  => Proof_Ins,
                   Reads      => Reads,
                   Writes     => Unused);

      --  Add Proof_Ins to Reads
      Reads.Union (Proof_Ins);

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
               if Reads.Contains (Change_Variant (Var, In_View))
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

      procedure Visitor (V  : Vertex_Id;
                         TV : out Simple_Traversal_Instruction);
      --  Emit a high check for all publically visible variables modified
      --  at this vertex.

      -------------
      -- Visitor --
      -------------

      procedure Visitor (V  : Vertex_Id;
                         TV : out Simple_Traversal_Instruction)
      is
         K : constant Flow_Id := FA.PDG.Get_Key (V);
      begin
         TV := Continue;

         if not Present (K) then
            return;
         end if;

         --  Only check nodes in the body
         if K.Kind in Direct_Mapping | Record_Field and then
           Get_Flow_Scope (K.Node).Part in Visible_Part | Private_Part
         then
            return;
         end if;

         for Var of Visible_Vars loop
            if FA.Atr (V).Variables_Defined.Contains (Var) then
               Error_Msg_Flow
                 (FA       => FA,
                  Msg      => "modification of & in elaboration requires " &
                    "Elaborate_Body on package &",
                  Severity => High_Check_Kind,
                  N        => Error_Location (FA.PDG, FA.Atr, V),
                  F1       => Var,
                  F2       => Direct_Mapping_Id (FA.Spec_Entity),
                  Tag      => Pragma_Elaborate_Body_Needed,
                  Vertex   => V);
            end if;
         end loop;
      end Visitor;

   --  Start of processing for Check_Elaborate_Body

   begin
      --  We only do this check when we use the gnat static elaboration
      --  model, since otherwise the front-end has a much more brutal
      --  method of enforcing this.
      if Dynamic_Elaboration_Checks then
         return;
      end if;

      --  We only apply this check to a package without Elaborate_Body. We
      --  do need to go up the tree as only the top-level package has this
      --  pragma applied.
      declare
         Ptr : Entity_Id := FA.Spec_Entity;
      begin
         while Present (Ptr) and then not Has_Pragma_Elaborate_Body (Ptr) loop
            Ptr := Scope (Ptr);
            pragma Assert (if Present (Ptr) then Nkind (Ptr) in N_Entity);
         end loop;
         if Present (Ptr) and then Has_Pragma_Elaborate_Body (Ptr) then
            return;
         end if;
      end;

      --  We only check packages that are in spec files. This tests if the
      --  package in question is nested in a body or not.
      declare
         Ptr : Node_Id   := FA.Spec_Entity;
         K   : Node_Kind := Node_Kind'First;
      begin
         --  We go up the chain, finding either specs or bodies. If the
         --  last thing we find was a spec, then we must be in a spec
         --  file.
         while Present (Ptr) loop
            if Nkind (Ptr) in N_Package_Specification | N_Package_Body then
               K := Nkind (Ptr);
            end if;
            Ptr := Parent (Ptr);
         end loop;
         if K /= N_Package_Specification then
            return;
         end if;
      end;

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
            begin
               if Is_Loop_Variable (Var) then
                  --  We do not check loop variables that are part of our
                  --  local context.
                  null;
               elsif Is_Initialized_At_Elaboration (Var, FA.S_Scope) and then
                 not Is_Constant (Var)
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

   procedure Check_Termination (FA : in out Flow_Analysis_Graphs) is
      Termination_Proved : constant Boolean :=
        not Is_Potentially_Nonreturning (FA.Analyzed_Entity);
   begin
      if Termination_Proved then
         Error_Msg_Flow (FA         => FA,
                         Msg        => "subprogram will terminate",
                         Severity   => Info_Kind,
                         N          => FA.Analyzed_Entity);
      else
         Error_Msg_Flow (FA         => FA,
                         Msg        => "subprogram may not terminate",
                         Severity   => Warning_Kind,
                         N          => FA.Analyzed_Entity);
      end if;
   end Check_Termination;

end Flow.Analysis;
