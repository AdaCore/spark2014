------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2015, Altran UK Limited                 --
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
with Flow.Analysis.Antialiasing;
with Flow.Analysis.Sanity;
with Flow_Debug;                  use Flow_Debug;
with Flow_Error_Messages;         use Flow_Error_Messages;
with Flow_Utility;                use Flow_Utility;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Output;                      use Output;
with Sem_Util;                    use Sem_Util;
with Sinfo;                       use Sinfo;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Util;                  use SPARK_Util;
with Stand;                       use Stand;
with VC_Kinds;                    use VC_Kinds;
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
     (G   : Flow_Graphs.T'Class;
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
      F : Flow_Id) return Node_Id;
   --  Find the given global F in the subprogram declaration of S (or
   --  in the initializes clause of S). If we can't find it (perhaps
   --  because of computed globals) we just return S which is a useful
   --  fallback place to raise an error.

   function Get_Initial_Vertex (G : Flow_Graphs.T;
                                F : Flow_Id)
                                return Flow_Graphs.Vertex_Id
     with Pre  => F.Variant = Normal_Use,
          Post => Get_Initial_Vertex'Result = Flow_Graphs.Null_Vertex
                    or else G.Get_Key (Get_Initial_Vertex'Result).Variant in
                              Initial_Value | Initial_Grouping;
   --  Returns the vertex id which represents the initial value for F

   function Get_Final_Vertex (G : Flow_Graphs.T;
                              F : Flow_Id)
                              return Flow_Graphs.Vertex_Id
     with Pre  => F.Variant = Normal_Use,
          Post => G.Get_Key
            (Get_Final_Vertex'Result).Variant = Final_Value;
   --  Returns the vertex id which represents the final value for F

   --------------------
   -- Error_Location --
   --------------------

   function Error_Location
     (G : Flow_Graphs.T'Class;
      M : Attribute_Maps.Map;
      V : Flow_Graphs.Vertex_Id) return Node_Or_Entity_Id
   is
      K : constant Flow_Id      := G.Get_Key (V);
      A : constant V_Attributes := M.Element (V);
   begin
      if Present (A.Error_Location) then
         return A.Error_Location;
      else
         case K.Kind is
            when Direct_Mapping | Record_Field =>
               return Get_Direct_Mapping_Id (K);
            when others =>
               raise Why.Unexpected_Node;
         end case;
      end if;
   end Error_Location;

   --------------
   -- Get_Line --
   --------------

   function Get_Line
     (G   : Flow_Graphs.T'Class;
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
      FD       : Ada.Text_IO.File_Type;
   begin
      if Set.Length > 1 then
         Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Filename);

         for V of Set loop
            declare
               F : constant Flow_Id := FA.PDG.Get_Key (V);
            begin
               if F.Kind = Direct_Mapping then
                  Ada.Text_IO.Put (FD, Get_Line (FA.PDG, FA.Atr, V));
                  Ada.Text_IO.New_Line (FD);
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
      First_Use : Node_Id;
   begin
      First_Use := First_Variable_Use
        (FA      => FA,
         Var     => Var,
         Kind    => Use_Any,
         Precise => True);

      if First_Use = FA.Analyzed_Entity then
         --  Ok, we did not actually find a node which makes use of
         --  Var, which is a bit odd. This means that the computed
         --  globals for FA.Analyzed_Entity contain a symbol Var for
         --  no good reason.
         Error_Msg_Flow
           (FA   => FA,
            Msg  => "bug: & contains reference to &, " &
              "but no use can be found",
            N    => FA.Analyzed_Entity,
            F1   => Direct_Mapping_Id (FA.Analyzed_Entity),
            F2   => Var,
            Kind => Error_Kind);

      else
         pragma Assert (Nkind (First_Use) in N_Subprogram_Call);

         Error_Msg_Flow
           (FA   => FA,
            Msg  => "called subprogram & requires GLOBAL " &
              "aspect to make state & visible",
            N    => First_Use,
            F1   => Direct_Mapping_Id (Get_Called_Entity (First_Use)),
            F2   => Var,
            Kind => Error_Kind);
      end if;
   end Global_Required;

   -----------------
   -- Find_Global --
   -----------------

   function Find_Global
     (S : Entity_Id;
      F : Flow_Id) return Node_Id
   is
      Needle     : Entity_Id;
      Haystack_A : Node_Id;
      Haystack_B : Node_Id;
      The_Global : Node_Id := Empty;

      function Find_It (N : Node_Id) return Traverse_Result;
      --  Checks if N refers to Needle and sets The_Global to N if
      --  that is the case.

      function Find_It (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N))
                 and then Nkind (Entity (N)) in N_Entity  -- ??? workaround
                 and then Unique_Entity (Entity (N)) = Needle
               then
                  The_Global := N;
                  return Abandon;
               else
                  return OK;
               end if;
            when others =>
               return OK;
         end case;
      end Find_It;

      procedure Look_For_Global is new Traverse_Proc (Find_It);

   --  Start of processing for Find_Global

   begin
      case Ekind (S) is
         when E_Package_Body =>
            Haystack_A := Empty;
            Haystack_B := Get_Pragma (Spec_Entity (S), Pragma_Initializes);

         when E_Package =>
            Haystack_A := Empty;
            Haystack_B := Get_Pragma (S, Pragma_Initializes);

         when Subprogram_Kind | E_Task_Type | E_Entry =>
            declare
               Body_E : constant Entity_Id := Get_Body_Entity (S);
            begin
               if Present (Body_E) then
                  Haystack_A := Get_Pragma (Body_E, Pragma_Refined_Global);
               else
                  Haystack_A := Empty;
               end if;
               Haystack_B := Get_Pragma (S, Pragma_Global);
            end;
         when others =>
            raise Why.Unexpected_Node;
      end case;

      case F.Kind is
         when Direct_Mapping | Record_Field =>
            Needle := Get_Direct_Mapping_Id (F);
            Look_For_Global (Haystack_A);
            if Present (The_Global) then
               return The_Global;
            end if;

            Look_For_Global (Haystack_B);
            if Present (The_Global) then
               return The_Global;
            else
               return S;
            end if;

         when Magic_String =>
            return S;

         when Null_Value | Synthetic_Null_Export =>
            raise Why.Unexpected_Node;
      end case;
   end Find_Global;

   ------------------------
   -- Get_Initial_Vertex --
   ------------------------

   function Get_Initial_Vertex (G : Flow_Graphs.T;
                                F : Flow_Id)
                                return Flow_Graphs.Vertex_Id
   is
   begin
      for V of G.Get_Collection (Flow_Graphs.All_Vertices) loop
         if Change_Variant (G.Get_Key (V), Normal_Use) = F then
            return V;
         end if;
      end loop;

      --  We could not find F's initial vertex
      return Flow_Graphs.Null_Vertex;
   end Get_Initial_Vertex;

   ----------------------
   -- Get_Final_Vertex --
   ----------------------

   function Get_Final_Vertex (G : Flow_Graphs.T;
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
         if Get_Variable_Set (N,
                              Scope                => Scope,
                              Local_Constants      => FA.Local_Constants,
                              Reduced              => not Precise,
                              Allow_Statements     => True,
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

         Atr         : constant V_Attributes := FA.Atr.Element (V);
         Check_Read  : constant Boolean      := Kind in Use_Read | Use_Any;
         Check_Write : constant Boolean      := Kind in Use_Write | Use_Any;
         Of_Interest : Boolean               := False;

      begin

         --  First we check if the current vertex contains the
         --  variable of interest.

         if Check_Read then
            if Atr.Variables_Used.Contains (Var_Normal) or else
              (not Precise and then
                 To_Entire_Variables (Atr.Variables_Used).Contains
                 (E_Var_Normal))
            then
               Of_Interest := True;
            end if;
         end if;
         if Check_Write then
            if Atr.Variables_Defined.Contains (Var_Normal) or else
              (not Precise and then
                 To_Entire_Variables (Atr.Variables_Defined).Contains
                 (E_Var_Normal))
            then
               Of_Interest := True;
            end if;
         end if;

         --  If not we stop here.

         if not Of_Interest then
            T_Ins := Flow_Graphs.Continue;
            return;
         else
            T_Ins := Flow_Graphs.Abort_Traversal;
         end if;

         --  Not all vertices containing the variable are actually
         --  interesting. We want to deal only with program statements
         --  and procedure calls.

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
            --  If we have a global, the procedure call itself is the
            --  best location we can provide.
            First_Use := Get_Direct_Mapping_Id (Atr.Call_Vertex);
            return;
         else
            --  If we don't have any of the above, we should keep
            --  searching for other, more suitable, vertices.
            T_Ins := Flow_Graphs.Continue;
            return;
         end if;

         --  We have found a suitable vertex. We can now narrow down
         --  the location to the individual subexpression which
         --  contains the variable.

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
   begin
      FA.CFG.BFS (Start         => FA.Start_Vertex,
                  Include_Start => False,
                  Visitor       => Proc'Access);
      return First_Use;
   end First_Variable_Use;

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

      for R of Reads loop
         --  ??? Fix this for magic strings once M711-031 is implemented
         if not (R.Kind in Direct_Mapping | Record_Field and then
                   Is_Initialized_At_Elaboration (Get_Direct_Mapping_Id (R),
                                                  FA.B_Scope))
         then
            Error_Msg_Flow
              (FA   => FA,
               Msg  => "& might not be initialized after elaboration " &
                 "of main program &",
               N    => Find_Global (FA.Analyzed_Entity, R),
               F1   => R,
               F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag  => Uninitialized,
               Kind => Medium_Check_Kind);
         end if;

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
         Sanity.Check_Variable_Free_Expressions'Access,
         Sanity.Check_Generated_Refined_Global'Access,
         Sanity.Check_Illegal_Writes'Access,
         Sanity.Check_All_Variables_Known'Access);
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
               when E_Entry           |
                    E_Subprogram_Body |
                    E_Task_Body       => (if Refined
                                          then "Refined_Global"
                                          else "Global"),
               when others => "Initializes");

            SRM_Ref : constant String :=
              (case FA.Kind is
               when E_Entry           |
                    E_Subprogram_Body |
                    E_Task_Body       => "6.1.4(13)",
               when E_Package         |
                    E_Package_Body    => "7.1.5(12)",
               when others            => raise Program_Error);

         begin
            if Refined then
               Vars_Known := To_Entire_Variables (FA.All_Vars);
            else
               case FA.Kind is
                  when E_Subprogram_Body | E_Entry =>
                     Vars_Known := Flow_Id_Sets.Empty_Set;

                     --  We need to assemble the variables known from
                     --  the spec: these are parameters and globals.
                     declare
                        E                   : Entity_Id;
                        Tmp_A, Tmp_B, Tmp_C : Flow_Id_Sets.Set;
                     begin
                        E := First_Formal (FA.Spec_Entity);
                        while Present (E) loop
                           Vars_Known.Include (Direct_Mapping_Id (E));
                           E := Next_Formal (E);
                        end loop;

                        Get_Globals (Subprogram => FA.Spec_Entity,
                                     Scope      => FA.S_Scope,
                                     Classwide  => False,
                                     Proof_Ins  => Tmp_A,
                                     Reads      => Tmp_B,
                                     Writes     => Tmp_C);
                        for F of To_Entire_Variables (Tmp_A or
                                                        Tmp_B or
                                                        Tmp_C)
                        loop
                           Vars_Known.Include (Change_Variant (F, Normal_Use));
                        end loop;
                     end;

                  when E_Package | E_Package_Body =>
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

                  when E_Task_Body =>
                     raise Program_Error;
               end case;
            end if;

            for Expr of Get_Postcondition_Expressions (FA.Spec_Entity,
                                                       Refined)
            loop
               case FA.Kind is
                  when E_Subprogram_Body =>
                     Vars_Used := To_Entire_Variables
                       (Get_Variable_Set
                          (Expr,
                           Scope                => Get_Flow_Scope (Expr),
                           Local_Constants      => FA.Local_Constants,
                           Fold_Functions       => False,
                           Reduced              => True,
                           Use_Computed_Globals => True));

                  when E_Task_Body =>
                     --  Nothing to do - no pre or postconditions.
                     null;

                  when others =>
                     Vars_Used := To_Entire_Variables
                       (Get_Variable_Set
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
                       (FA      => FA,
                        Msg     => "& must be listed in the " &
                                      Aspect_To_Fix & " aspect of &",
                        SRM_Ref => SRM_Ref,
                        N       => First_Variable_Use (N       => Expr,
                                                       FA      => FA,
                                                       Scope   => FA.B_Scope,
                                                       Var     => Var,
                                                       Precise => False),
                        F1      => Entire_Variable (Var),
                        F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Kind    => Error_Kind);
                     Sane := False;

                  elsif FA.Kind in E_Package | E_Package_Body
                    and then Is_Library_Level_Entity (FA.Analyzed_Entity)
                    and then not Is_Initialized_At_Elaboration (Var,
                                                                FA.B_Scope)
                  then

                     --  To check an initial_condition aspect, we make sure
                     --  that all variables mentioned are also mentioned in
                     --  an initializes aspect.

                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "& must be initialized at elaboration",
                        N    => First_Variable_Use (N       => Expr,
                                                    FA      => FA,
                                                    Scope   => FA.B_Scope,
                                                    Var     => Var,
                                                    Precise => False),
                        F1   => Entire_Variable (Var),
                        Kind => Error_Kind);
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
      F_Final   : Flow_Id;
      A_Final   : V_Attributes;
      F_Initial : Flow_Id;
      A_Initial : V_Attributes;
      Unwritten : Boolean;

      Written_Entire_Vars : Flow_Id_Sets.Set;
      Unwritten_Vars      : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         F_Final := FA.PDG.Get_Key (V);
         A_Final := FA.Atr.Element (V);
         if F_Final.Variant = Final_Value and then
           A_Final.Is_Export
         then

            --  We have a final use vertex which is an export that has
            --  a single in-link. If this in-link is its initial value
            --  then clearly we do not set this output on any path.

            Unwritten := False;
            if FA.PDG.In_Neighbour_Count (V) = 1 then
               F_Initial := FA.PDG.Get_Key (FA.PDG.Parent (V));
               A_Initial := FA.Atr.Element (FA.PDG.Parent (V));
               if F_Initial.Variant = Initial_Value and then
                 A_Initial.Is_Import and then
                 Change_Variant (F_Initial, Final_Value) = F_Final
               then
                  Unwritten := True;
               end if;
            end if;

            if Unwritten then
               Unwritten_Vars.Include (V);
            else
               Written_Entire_Vars.Include (Entire_Variable (F_Final));
            end if;
         end if;
      end loop;

      for V of Unwritten_Vars loop
         F_Final := FA.PDG.Get_Key (V);
         A_Final := FA.Atr.Element (V);

         if not Written_Entire_Vars.Contains (Entire_Variable (F_Final)) then

            if not (F_Final.Kind in Direct_Mapping | Record_Field)
              or else not FA.Unmodified_Vars.Contains
                            (Get_Direct_Mapping_Id (F_Final))
            then

               if A_Final.Is_Global then
                  Error_Msg_Flow
                    (FA     => FA,
                     Msg    => "& is not modified, could be INPUT",
                     N      => Find_Global (FA.Analyzed_Entity, F_Final),
                     F1     => Entire_Variable (F_Final),
                     Tag    => Inout_Only_Read,
                     Kind   => Warning_Kind,
                     Vertex => V);
               else
                  Error_Msg_Flow
                    (FA     => FA,
                     Msg    => "& is not modified, could be IN",
                     N      => Error_Location (FA.PDG, FA.Atr, V),
                     F1     => Entire_Variable (F_Final),
                     Tag    => Inout_Only_Read,
                     Kind   => Warning_Kind,
                     Vertex => V);
               end if;
            end if;
         end if;
      end loop;
   end Find_Unwritten_Exports;

   -------------------------------------------------
   -- Find_Ineffective_Imports_And_Unused_Objects --
   -------------------------------------------------

   procedure Find_Ineffective_Imports_And_Unused_Objects
     (FA : in out Flow_Analysis_Graphs)
   is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean
      is (FA.PDG.Get_Key (V).Variant = Final_Value and then
            FA.Atr.Element (V).Is_Export)
        or else FA.Atr.Element (V).Is_Precondition
        or else FA.Atr.Element (V).Is_Postcondition
        or else FA.Atr.Element (V).Is_Proof;
      --  Checks if the given vertex V is a final-use vertex or is useful for
      --  proof.

      Suppressed_Entire_Ids : Flow_Id_Sets.Set;
      --  Entire variables appearing in a "null => Blah" dependency relation;
      --  for these we suppress the ineffective import warning.

      EV_Considered_Imports : Flow_Id_Sets.Set;
      EV_Considered_Objects : Flow_Id_Sets.Set;
      --  Sets of entire variables marking all objects considered for each
      --  of the two analyses.

      EV_Used               : Flow_Id_Sets.Set;
      --  For variables we have at least used once somewhere (even if its
      --  not effective).

      EV_Effective          : Flow_Id_Sets.Set;
      --  For variables where we use at least a part (for example an
      --  individual component of a record, or the bounds of an
      --  unconstrained array) to determine the final value of at least one
      --  export.

      EV_Unused             : Flow_Id_Sets.Set;
      EV_Ineffective        : Flow_Id_Sets.Set;

   begin

      --  We look at the null depends (if one exists). For any variables
      --  mentioned there, we suppress the ineffective import warning.

      Suppressed_Entire_Ids := Flow_Id_Sets.Empty_Set;
      if FA.Kind = E_Subprogram_Body and then Present (FA.Depends_N) then
         declare
            D : Dependency_Maps.Map;
         begin
            Get_Depends (Subprogram => FA.Analyzed_Entity,
                         Scope      => FA.B_Scope,
                         Classwide  => False,
                         Depends    => D);
            if D.Contains (Null_Flow_Id) then
               Suppressed_Entire_Ids := D (Null_Flow_Id);
            end if;
         end;
      end if;

      pragma Assert_And_Cut (True);

      --  We now detect all imports that are ineffective (do not contribute
      --  to at least one export) and objects that are never used.

      EV_Considered_Imports := Flow_Id_Sets.Empty_Set;
      EV_Considered_Objects := Flow_Id_Sets.Empty_Set;
      EV_Used               := Flow_Id_Sets.Empty_Set;
      EV_Effective          := Flow_Id_Sets.Empty_Set;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr : constant V_Attributes := FA.Atr.Element (V);

            E              : Flow_Id;
            Disuse_Not_Bad : Boolean;
            Skip_This      : Boolean;
         begin
            if Key.Variant = Initial_Value and then
              Key.Kind /= Synthetic_Null_Export
            then

               --  Note the entire variable.

               E := Change_Variant (Entire_Variable (Key), Normal_Use);

               --  If this is a bound variable or discriminant, we only
               --  consider it if its actually used. Its not an error to
               --  not explicitly use it.

               Disuse_Not_Bad := Is_Bound (Key) or Is_Discriminant (Key);

               --  Generally we allow a discriminant or bound to mark the
               --  entire variable as used (if its used) and otherwise
               --  have no effect (not using it is not flagging the entire
               --  variable as unused). However this is only valid for out
               --  parameters; for in out parameters the value of the
               --  entire variable itself has to be used and the bounds are
               --  completely optional.

               Skip_This := (if Disuse_Not_Bad
                             then Atr.Mode = Mode_In_Out
                             else False);

               --  Determine ineffective imports.

               if not Skip_This then

                  if Atr.Is_Initialized and Atr.Is_Import then
                     if not Disuse_Not_Bad then
                        EV_Considered_Imports.Include (E);
                     end if;

                     --  Check if we're ineffective or not. If not, we note
                     --  that we at least partially have used the entire
                     --  variable.

                     if FA.PDG.Non_Trivial_Path_Exists (V,
                                                        Is_Final_Use'Access)
                     then
                        if Disuse_Not_Bad then
                           EV_Considered_Imports.Include (E);
                        end if;
                        EV_Effective.Include (E);
                     end if;
                  end if;

                  --  Determine unused objects.

                  if not Disuse_Not_Bad then
                     EV_Considered_Objects.Include (E);
                  end if;

                  if FA.PDG.Out_Neighbour_Count (V) = 1 then
                     declare
                        Final_V : constant Flow_Graphs.Vertex_Id :=
                          FA.PDG.Child (V);
                     begin
                        if FA.PDG.Get_Key (Final_V).Variant /= Final_Value
                          or else FA.PDG.In_Neighbour_Count (Final_V) > 1
                        then
                           if Disuse_Not_Bad then
                              EV_Considered_Objects.Include (E);
                           end if;
                           EV_Used.Include (E);
                        end if;
                     end;
                  else
                     if Disuse_Not_Bad then
                        EV_Considered_Objects.Include (E);
                     end if;
                     EV_Used.Include (E);
                  end if;
               end if;
            end if;
         end;
      end loop;

      pragma Assert_And_Cut
        (EV_Considered_Imports.Length >= EV_Effective.Length and
         EV_Considered_Objects.Length >= EV_Used.Length);

      --  Now that we can issue error messages. We can't do it inline (i.e.
      --  on detection above) because we need to pay special attention to
      --  records and unconstrained arrays.

      --  First we issue warnings on unused objects.

      EV_Unused := EV_Considered_Objects - EV_Used;

      for F of EV_Unused loop
         declare
            V : constant Flow_Graphs.Vertex_Id := Get_Initial_Vertex (FA.PDG,
                                                                      F);
            A : constant V_Attributes          := FA.Atr.Element (V);
         begin
            if A.Is_Global then
               --  We have an unused global, we need to give the error
               --  on the subprogram, instead of on the global. In
               --  generative mode we don't emit this message.
               if not FA.Is_Generative then
                  if Is_Variable (F) then
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "unused global &",
                        N        => Find_Global (FA.Analyzed_Entity, F),
                        F1       => F,
                        Tag      => Unused,
                        Kind     => Low_Check_Kind);
                  else
                     --  Issue a different message if the global is a constant.
                     Error_Msg_Flow
                       (FA       => FA,
                        Msg      => "& cannot appear in Globals",
                        N        => Find_Global (FA.Analyzed_Entity, F),
                        F1       => F,
                        Tag      => Unused,
                        Kind     => Medium_Check_Kind);
                  end if;
               end if;
            else
               --  We suppress this warning when we are dealing with a
               --  protected type.
               if not (F.Kind = Direct_Mapping)
                 or else Ekind (Get_Direct_Mapping_Id (F)) /= E_Protected_Type
               then
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "unused variable &",
                     N    => Error_Location (FA.PDG, FA.Atr, V),
                     F1   => F,
                     Tag  => Unused,
                     Kind => Warning_Kind);
               end if;
            end if;
         end;
      end loop;

      pragma Assert_And_Cut
        (EV_Considered_Imports.Length >= EV_Effective.Length and
         EV_Considered_Objects.Length >= EV_Used.Length);

      --  Finally, we issue warnings on ineffective imports. We exclude
      --  items which are suppressed by a null derives and which have
      --  previously been flagged as unused. In the loop below we further
      --  exclude objects that are marked by a pragma Unreferenced.

      EV_Ineffective := EV_Considered_Imports -
        (EV_Effective or Suppressed_Entire_Ids or EV_Unused);

      for F of EV_Ineffective loop
         declare
            V   : constant Flow_Graphs.Vertex_Id := Get_Initial_Vertex (FA.PDG,
                                                                        F);
            Atr : constant V_Attributes          := FA.Atr.Element (V);
         begin
            if F.Kind in Direct_Mapping | Record_Field and then
              FA.Unreferenced_Vars.Contains (Get_Direct_Mapping_Id (F))
            then
               --  This variable is marked with a pragma Unreferenced, so
               --  we do not emit the warning here.
               null;
            elsif Atr.Mode = Mode_Proof then
               --  Proof_Ins are never ineffective imports, for now.
               null;
            elsif Atr.Is_Global then
               if FA.Kind = E_Subprogram_Body
                 and then not FA.Is_Generative
               then
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => (if FA.B_Scope.Section /= Body_Part
                                and then Is_Abstract_State (F)
                                and then Present (FA.B_Scope)
                                and then State_Refinement_Is_Visible
                                           (Get_Direct_Mapping_Id (F),
                                            Body_Scope (FA.B_Scope))
                              then "non-visible constituents " &
                                   "of & are not used " &
                                   "- consider moving the subprogram to the " &
                                   "package body and adding a Refined_Global"
                              else "unused initial value of &"),
                     N    => Find_Global (FA.Analyzed_Entity, F),
                     F1   => F,
                     F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag  => Unused_Initial_Value,
                     Kind => Warning_Kind);
               end if;
            else
               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "unused initial value of &",
                  --  ??? find_import
                  N    => Error_Location (FA.PDG, FA.Atr, V),
                  F1   => F,
                  F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag  => Unused_Initial_Value,
                  Kind => Warning_Kind);
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
      --  If F is used but is not declared in the compilation unit
      --  enclosing the currently analyzed entity AND the other
      --  compilation unit does not have an Elaborate_All then emit an
      --  error.

      ---------------------------------------------
      -- Check_If_From_Another_Non_Elaborated_CU --
      ---------------------------------------------

      procedure Check_If_From_Another_Non_Elaborated_CU
        (F : Flow_Id;
         V : Flow_Graphs.Vertex_Id)
      is

         function Get_Enclosing_Comp_Unit (Start : Node_Id) return Node_Id;
         --  Goes up the tree and returns the first N_Compilation_Unit
         --  that it finds.

         -----------------------------
         -- Get_Enclosing_Comp_Unit --
         -----------------------------

         function Get_Enclosing_Comp_Unit (Start : Node_Id) return Node_Id is
            Current_Unit : Node_Id := Start;
         begin
            while Present (Current_Unit)
              and then Nkind (Current_Unit) /= N_Compilation_Unit
            loop
               Current_Unit := Parent (Current_Unit);
            end loop;

            return Current_Unit;
         end Get_Enclosing_Comp_Unit;

         N     : constant Node_Id := (if F.Kind = Direct_Mapping
                                      then Get_Direct_Mapping_Id (F)
                                      else Empty);

         V_Use : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
         V_Atr : V_Attributes;
      begin
         --  Find a non-'Final vertex where the state abstraction is
         --  used. If the state abstraction is not used then we do not
         --  issue an error.
         for Neighbour of FA.PDG.Get_Collection (V,
                                                 Flow_Graphs.Out_Neighbours)
         loop
            declare
               Key : constant Flow_Id := FA.PDG.Get_Key (Neighbour);
            begin
               if Key.Variant /= Final_Value
                 or else Change_Variant (Entire_Variable (Key),
                                         Normal_Use) /= F
               then
                  V_Use := Neighbour;
                  V_Atr := FA.Atr.Element (Neighbour);
                  exit;
               end if;
            end;
         end loop;

         if Present (N)
           and then V_Use /= Flow_Graphs.Null_Vertex
           and then Is_Compilation_Unit (Scope (N))
           and then (Scope (N) /= FA.Analyzed_Entity
                       and then Scope (N) /= FA.Spec_Entity)
         then
            declare
               Clause       : Node_Id;
               Current_Unit : constant Node_Id :=
                 Get_Enclosing_Comp_Unit (FA.Spec_Entity);
               Other_Unit   : constant Node_Id :=
                 Get_Enclosing_Comp_Unit (Scope (N));
            begin
               Clause := First (Context_Items (Current_Unit));
               while Present (Clause) loop
                  if Nkind (Clause) = N_With_Clause
                    and then Library_Unit (Clause) = Other_Unit
                  then
                     if not Elaborate_All_Present (Clause) then
                        Error_Msg_Flow
                          (FA      => FA,
                           Msg     => "use of remote abstract state &" &
                                      " during elaboration of &" &
                                      " - Elaborate_All pragma required for &",
                           SRM_Ref => "7.7.1(4)",
                           N       => V_Atr.Error_Location,
                           F1      => F,
                           F2      => Direct_Mapping_Id (FA.Spec_Entity),
                           F3      => Direct_Mapping_Id (Scope (N)),
                           Kind    => Error_Kind,
                           Tag     => Pragma_Elaborate_All_Needed);
                     end if;

                     return;
                  end if;

                  Next (Clause);
               end loop;
            end;
         end if;
      end Check_If_From_Another_Non_Elaborated_CU;
   begin
      --  If we are not analyzing a compilation unit then there is
      --  nothing to do here.
      if not Is_Compilation_Unit (FA.Analyzed_Entity) then
         return;
      end if;

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id := FA.PDG.Get_Key (V);
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
      --  Checks if the given vertex V is a final-use vertex that is
      --  also an export.

      function Is_Final_Use_Unreferenced (V : Flow_Graphs.Vertex_Id)
                                          return Boolean;
      --  Checks if the given vertex V is a final-use vertex that
      --  corresponds to a variable that is mentioned in a pragma
      --  Unreferenced.

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
         Vars_Defined : constant Flow_Id_Sets.Set :=
           FA.Atr.Element (V).Variables_Defined;
      begin
         for Var_Def of Vars_Defined loop
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
         Vars_Defined : constant Flow_Id_Sets.Set :=
           FA.Atr.Element (Ineffective_Statement).Variables_Defined;

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction);
         --  Check if V masks the ineffective statement.

         procedure Visitor
           (V  : Flow_Graphs.Vertex_Id;
            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
            Intersection : constant Flow_Id_Sets.Set :=
              Vars_Defined and
              (FA.Atr.Element (V).Variables_Defined -
                 FA.Atr.Element (V).Variables_Used);
         begin
            if V /= Ineffective_Statement and then
              Intersection.Length >= 1
            then
               Mask.Include (V);
               TV := Flow_Graphs.Skip_Children;
            else
               TV := Flow_Graphs.Continue;
            end if;
         end Visitor;

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
                                 return Boolean is
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

         procedure Visitor (V  : Flow_Graphs.Vertex_Id;
                            TV : out Flow_Graphs.Simple_Traversal_Instruction)
         is
            Atr : constant V_Attributes := FA.Atr.Element (V);
         begin
            if Atr.Execution /= Normal_Execution then
               TV := Flow_Graphs.Skip_Children;
            elsif V = FA.Helper_End_Vertex then
               Dead_End := False;
               TV := Flow_Graphs.Abort_Traversal;
            else
               TV := Flow_Graphs.Continue;
            end if;
         end Visitor;
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
         return FA.PDG.Get_Key (V).Variant = Final_Value and then
           FA.Atr.Element (V).Is_Export;
      end Is_Final_Use_Any_Export;

      -------------------------------
      -- Is_Final_Use_Unreferenced --
      -------------------------------

      function Is_Final_Use_Unreferenced (V : Flow_Graphs.Vertex_Id)
                                          return Boolean
      is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value and then
           FA.Unreferenced_Vars.Contains
             (Get_Direct_Mapping_Id (Change_Variant
                                       (FA.PDG.Get_Key (V), Normal_Use)));
      end Is_Final_Use_Unreferenced;

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
            declare
               VS : constant Vertex_Sets.Set := FA.Other_Fields.Element (V);
            begin
               for Other_Field of VS loop
                  if FA.PDG.Non_Trivial_Path_Exists
                    (Other_Field, Is_Final_Use_Any_Export'Access)
                  then
                     return False;
                  end if;
               end loop;
            end;
         end if;

         --  If we reach this point then all other fields are
         --  ineffective.
         return True;
      end Other_Fields_Are_Ineffective;

   begin --  Find_Ineffective_Statements
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            N         : Node_Id;
            Key       : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr       : constant V_Attributes := FA.Atr.Element (V);
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
                 (if FA.Kind in E_Package | E_Package_Body
                    and then No (FA.Initializes_N)
                  then
                     not FA.PDG.Non_Trivial_Path_Exists
                       (V, Is_Any_Final_Use'Access)) and then

                 --  Suppression for vertices that lead to a final
                 --  vertex that corresponds to a variable that is
                 --  mentioned in a pragma unreferenced.
                 not FA.PDG.Non_Trivial_Path_Exists
                       (V, Is_Final_Use_Unreferenced'Access) and then

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
                        --  For in parameters we do not emit the
                        --  ineffective assignment error as its a bit
                        --  confusing.
                        null;

                     elsif Atr.Is_Global_Parameter and then
                       Atr.Parameter_Formal.Variant = In_View
                     then
                        --  Ditto for globals in views.
                        null;

                     elsif Atr.Is_Discr_Or_Bounds_Parameter or
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
                           Kind      => Warning_Kind);

                     else
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "unused assignment",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           Tag       => Tag,
                           Kind      => Warning_Kind,
                           Vertex    => V);
                     end if;

                  elsif Nkind (N) = N_Assignment_Statement then
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "unused assignment",
                        N         => Error_Location (FA.PDG, FA.Atr, V),
                        Tag       => Tag,
                        Kind      => Warning_Kind,
                        Vertex    => V);

                  elsif Nkind (N) = N_Object_Declaration then
                     if not Constant_Present (N) then
                        --  This warning is ignored for local constants.
                        Get_Name_String (Chars (Defining_Identifier (N)));
                        Adjust_Name_Case (Sloc (N));

                        if FA.Kind in E_Package | E_Package_Body
                          and then No (Find_Node_In_Initializes
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
                              Kind      => Warning_Kind,
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
                              Kind      => Warning_Kind,
                              Vertex    => V);
                        end if;

                     end if;

                  else
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "statement has no effect",
                        Kind      => Warning_Kind,
                        N         => Error_Location (FA.PDG, FA.Atr, V),
                        Tag       => Tag,
                        Vertex    => V);

                  end if;
                  if Mask.Length >= 1 then
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

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
      begin
         Dead_Code.Exclude (V);
         TV := Flow_Graphs.Continue;
      end Flag_Live;

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

   begin
      --  Guilty until proven innocent.
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : constant V_Attributes := FA.Atr.Element (V);
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
         declare
            A : constant V_Attributes := FA.Atr.Element (V);
         begin
            Error_Msg_Flow (FA     => FA,
                            Msg    => "this statement is never reached",
                            Kind   => Warning_Kind,
                            N      => A.Error_Location,
                            Tag    => VC_Kinds.Dead_Code,
                            Vertex => V);
         end;
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
      --  Returns True iff V should be considered for uninitialized
      --  variables.
      --
      --  We consider all vertices except for:
      --     * exceptional ones and
      --     * synthetic null output.

      procedure Mark_Definition_Free_Path
        (From      : Flow_Graphs.Vertex_Id;
         To        : Flow_Graphs.Vertex_Id;
         Var       : Flow_Id;
         V_Allowed : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
      --  Write a trace file that marks the path From -> To which does not
      --  define Var. If V_Allowed is set, then the path that we return is
      --  allowed to contain V_Allowed even if V_Allowed does set Var.

      procedure Might_Be_Defined_In_Other_Path
        (V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id;
         Found     : out Boolean;
         V_Error   : out Flow_Graphs.Vertex_Id);
      --  Sets Found when the variable corresponding to V_Initial is
      --  defined on a path that lead to V_Use. V_Error is the vertex
      --  where the message should be emitted.

      procedure Emit_Message (Var              : Flow_Id;
                              Vertex           : Flow_Graphs.Vertex_Id;
                              Is_Initialized   : Boolean;
                              Is_Uninitialized : Boolean)
      with Pre => Is_Initialized or Is_Uninitialized;
      --  Produces an appropriately worded info/low/high message for the
      --  given variable Var at the given location Vertex.
      --
      --  Is_Initialized should be set if there is at least one sensible
      --  read.
      --
      --  Is_Uninitialized should be set if there is at least one read from
      --  an uninitialized variable.
      --
      --  They can be both set, in which case we're most likely going to
      --  produce a medium check, but this is not always the case in loops.

      function Consider_Vertex (V : Flow_Graphs.Vertex_Id) return Boolean is
         V_Key : constant Flow_Id      := FA.PDG.Get_Key (V);
         V_Atr : constant V_Attributes := FA.Atr.Element (V);
      begin
         --  Ignore exceptional paths
         if V_Atr.Is_Exceptional_Path then
            return False;
         end if;

         --  Ignore synthetic null output
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
            A : constant V_Attributes := FA.Atr.Element (V);
         begin
            if V = To then
               Instruction := Flow_Graphs.Found_Destination;
               Path_Found  := True;
            elsif V /= V_Allowed
              and then A.Variables_Defined.Contains (Var)
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
            F : constant Flow_Id := FA.CFG.Get_Key (V);
         begin
            if V /= To and F.Kind = Direct_Mapping then
               Path.Include (V);
            end if;
         end Add_Loc;

      begin --  Mark_Definition_Free_Path
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
              and then Is_Type (Etype (The_Var.Node))
              and then Has_Array_Type (Etype (The_Var.Node)))
           or else
           (The_Var.Kind = Record_Field
              and then The_Var.Facet = Normal_Part
              and then Is_Type (Etype (The_Var.Component.Last_Element))
              and then Has_Array_Type
                         (Etype (The_Var.Component.Last_Element)));
         --  Notes if The_Var refers to an array.

         Use_Vertex_Points_To_Itself : constant Boolean :=
           (for some V of FA.PDG.Get_Collection (V_Use,
                                                 Flow_Graphs.Out_Neighbours)
              => V = V_Use);
         --  Notes if V_Use belongs to V_Use's Out_Neighbours

         Use_Execution_Is_Unconditional : constant Boolean :=
           (for some V of FA.PDG.Get_Collection (V_Use,
                                                 Flow_Graphs.In_Neighbours)
              => V = FA.Start_Vertex);
         --  Notes if FA.Start_Vertex is among the In_Neighbours of
         --  V_Use in the PDG (in other words, there is no control
         --  dependence on V).

         function Find_Explicit_Use_Vertex return Flow_Graphs.Vertex_Id;
         --  Find a vertex that explicitly uses The_Var and hangs off
         --  vertex V_Use in the CFG graph. If such a node does NOT
         --  exist, then Null_Vertex is returned.

         function Start_To_V_Def_Without_V_Use
           (V_Def : Flow_Graphs.Vertex_Id)
            return Boolean;
         --  Returns True if there exists a path in the CFG graph from
         --  Start to V_Def that does not cross V_Use.

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

            procedure Found_V_Exp_Use
              (V  : Flow_Graphs.Vertex_Id;
               TV : out Flow_Graphs.Simple_Traversal_Instruction)
            is
            begin
               if V = V_Use then
                  TV := Flow_Graphs.Skip_Children;
               elsif V /= Flow_Graphs.Null_Vertex
                 and then FA.Atr.Element (V).Variables_Defined.Contains
                 (The_Var)
               then
                  TV := Flow_Graphs.Skip_Children;
               elsif V /= Flow_Graphs.Null_Vertex
                 and then FA.CFG.Get_Key (V).Variant /= Final_Value
                 and then FA.Atr.Element (V).Variables_Explicitly_Used.Contains
                   (The_Var)
               then
                  V_Exp_Use := V;
                  TV := Flow_Graphs.Abort_Traversal;
               else
                  TV := Flow_Graphs.Continue;
               end if;
            end Found_V_Exp_Use;

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
            --  Stops the DFS search when we reach V_Def and skips the
            --  children of V_Use.

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

               --  If we reach the start vertex (remember, this
               --  traversal is going backwards through the CFG) or
               --  ourselves, then we should look for another path.

               TV := Flow_Graphs.Skip_Children;

            else

               TV := Flow_Graphs.Continue;
               if FA.Atr.Element (V).Variables_Defined.Contains (The_Var) then

                  --  OK, so this vertex V does define The_Var. There
                  --  are a few cases where we can possibly issue a
                  --  warning instead of an error.

                  if Start_To_V_Def_Without_V_Use (V_Def => V) then
                     --  There is a path from start -> this definition
                     --  V, that does not use V (but subsequenty
                     --  reaches V).

                     Found := True;
                     TV    := Flow_Graphs.Abort_Traversal;

                  elsif not Use_Execution_Is_Unconditional then
                     --  If the execution of v_use is predicated on
                     --  something else, then there might be a path
                     --  that defines the_var first.

                     Found := True;
                     TV    := Flow_Graphs.Abort_Traversal;
                  end if;
               end if;

            end if;

         end Vertex_Defines_Variable;

      begin --  Might_Be_Defined_In_Other_Path

         --  We initialize V_Print to V_Use and we shall change it
         --  later on if so required. Ditto for Found.

         Found   := False;
         V_Error := V_Use;

         --  Check if there might be some path that defines the
         --  variable before we use it.

         FA.CFG.DFS (Start         => V_Use,
                     Include_Start => False,
                     Visitor       => Vertex_Defines_Variable'Access,
                     Reversed      => True);

         --  Arrays that are partially defined have an implicit
         --  dependency on themselves. For this check, we cannot
         --  depend on the Variables_Used because they capture this
         --  implicit dependency. Instead, we use
         --  Variables_Explicitly_Used.

         if not Found and then Use_Vertex_Points_To_Itself then
            case The_Var.Kind is
               when Direct_Mapping | Record_Field =>
                  --  Check if node corresponds to an array.
                  if The_Var_Is_Array
                    and then not FA.Atr.Element
                      (V_Use).Variables_Explicitly_Used.Contains (The_Var)
                  then
                     --  We set Found and we then check if
                     --  there exists a vertex that explicitly uses The_Var,
                     --  if so, we set V_Print to that vertex.

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

         V_Key        : constant Flow_Id      := FA.PDG.Get_Key (Vertex);
         V_Atr        : constant V_Attributes := FA.Atr.Element (Vertex);

         V_Initial    : constant Flow_Graphs.Vertex_Id :=
           FA.PDG.Get_Vertex (Change_Variant (Var, Initial_Value));
         Atr_Initial  : constant V_Attributes := FA.Atr.Element (V_Initial);

         Kind         : Msg_Kind :=
           (if Is_Initialized and Is_Uninitialized then Unknown
            elsif Is_Initialized                   then Init
            else                                        Err);

         N            : Node_Id           := V_Atr.Error_Location;
         Msg          : Unbounded_String;

         V_Error      : Flow_Graphs.Vertex_Id;
         V_Goal       : Flow_Graphs.Vertex_Id;
         V_Allowed    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;

         Is_Final_Use : constant Boolean := V_Key.Variant = Final_Value;
         Is_Global    : constant Boolean := Atr_Initial.Is_Global;
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

         case Kind is
            when Init =>
               Msg := To_Unbounded_String ("initialization of & proved");
            when Unknown =>
               Msg := (if Default_Init
                       then To_Unbounded_String
                              ("input value of & might be used")
                       else To_Unbounded_String ("& might not be "));
            when Err =>
               Msg := (if Default_Init
                       then To_Unbounded_String
                              ("input value of & will be used")
                       else To_Unbounded_String ("& is not "));
         end case;

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
              (N        => Error_Location (FA.PDG,
                                           FA.Atr,
                                           V_Error),
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
            pragma Assert (Var.Node = FA.Analyzed_Entity);
            --  We special case this, so we don't emit "X" is initialized
            --  messages for the "variable" we use to model the value of
            --  the function return.
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
            Kind      => (case Kind is
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
           and then FA.Kind in E_Package | E_Package_Body
           and then Present (FA.Initializes_N)
         then
            Msg := To_Unbounded_String
              ("initialization of & is specified @");
            Error_Msg_Flow
              (FA           => FA,
               Tracefile    => Tracefile,
               Msg          => To_String (Msg),
               N            => N,
               F1           => Direct_Mapping_Id
                                 (Encapsulating_State (Var.Node)),
               F2           => Direct_Mapping_Id (FA.Initializes_N),
               Tag          => Uninitialized,
               Kind         => (case Kind is
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

      V_Atr            : V_Attributes;
      Def_Atr          : V_Attributes;
      Def_Key          : Flow_Id;
      Var_Atr          : V_Attributes;
      Is_Uninitialized : Boolean;
      Is_Initialized   : Boolean;

   begin --  Find_Use_Of_Uninitialized_Variables

      --  We look at all vertices except for:
      --     * exceptional ones and
      --     * synthetic null output
      for V of FA.DDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         V_Atr := FA.Atr.Element (V);
         if Consider_Vertex (V) then
            --  For each variable read...
            for Var_Read of V_Atr.Variables_Used loop
               Is_Uninitialized := False;
               Is_Initialized   := False;
               Var_Atr          := FA.Atr.Element
                 (FA.PDG.Get_Vertex (Change_Variant
                                       (Var_Read, Initial_Value)));

               if not Var_Atr.Is_Initialized
                 and then (if Ekind (FA.Analyzed_Entity) in
                             E_Package | E_Package_Body
                           then not Is_Abstract_State (Var_Read))
                 and then (if Var_Read.Kind in Direct_Mapping | Record_Field
                           then not Is_Constant_Object
                                      (Get_Direct_Mapping_Id (Var_Read)))
               then
                  --  ... we check the in neighbours in the DDG and see if
                  --  they define it. We record initialized / uninitialized
                  --  reads accordingly.
                  --
                  --  Note we skip this check for abstract state iff we
                  --  analyze a package, since it is OK to leave some state
                  --  uninitialized (Check_Initializes_Contract will pick
                  --  this up).
                  for V_Def of FA.DDG.Get_Collection
                    (V, Flow_Graphs.In_Neighbours)
                  loop
                     Def_Atr := FA.Atr.Element (V_Def);
                     Def_Key := FA.DDG.Get_Key (V_Def);
                     if Def_Key.Variant = Initial_Value
                       and then Change_Variant (Def_Key, Normal_Use) = Var_Read
                     then
                        --  We're using the initial value.
                        if Def_Atr.Is_Initialized then
                           Is_Initialized   := True;
                        else
                           Is_Uninitialized := True;
                        end if;
                     elsif Def_Atr.Variables_Defined.Contains (Var_Read)
                       or else Def_Atr.Volatiles_Read.Contains (Var_Read)
                     then
                        --  We're using a previously written value.
                        Is_Initialized := True;
                     end if;
                  end loop;

                  --  Some useful debug output before we issue the message.
                  if Debug_Trace_Check_Reads then
                     Write_Str ("@" & FA.DDG.Vertex_To_Natural (V)'Img);
                     if Is_Initialized then
                        Write_Str (" INIT");
                     end if;
                     if Is_Uninitialized then
                        Write_Str (" DIRTY");
                     end if;
                     Write_Str (" :");
                     Print_Flow_Id (Var_Read);
                  end if;

                  Emit_Message (Var              => Var_Read,
                                Vertex           => V,
                                Is_Initialized   => Is_Initialized,
                                Is_Uninitialized => Is_Uninitialized);
               end if;
            end loop;
         end if;
      end loop;

   end Find_Use_Of_Uninitialized_Variables;

   --------------------------
   -- Find_Stable_Elements --
   --------------------------

   procedure Find_Stable_Elements (FA : in out Flow_Analysis_Graphs) is
      Done      : Boolean            := False;
      M         : Attribute_Maps.Map := FA.Atr;
      Is_Stable : Boolean;
   begin
      for Loop_Id of FA.Loops loop
         Done := False;
         while not Done loop
            Done := True;
            for N_Loop of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr : V_Attributes := M (N_Loop);
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
                        M (N_Loop) := Atr;

                        --  Complain
                        Error_Msg_Flow
                          (FA     => FA,
                           Msg    => "stable",
                           N      => Error_Location (FA.PDG,
                                                     FA.Atr,
                                                     N_Loop),
                           Tag    => Stable,
                           Kind   => Warning_Kind,
                           Vertex => N_Loop);

                        --  There might be other stable elements now.
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
         --  Returns the smallest set of vertices that make up a path
         --  from "From" to "To" (excluding vertices "From" and "To").
         --  By default it operates on the PDG graph. If CFG_Graph is
         --  set to True then it operates on the CFG graph.

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
            --  Step procedure for Shortest_Path.

            procedure Are_We_There_Yet
              (V           : Flow_Graphs.Vertex_Id;
               Instruction : out Flow_Graphs.Traversal_Instruction);
            --  Visitor procedure for Shortest_Path.

            ---------------
            --  Add_Loc  --
            ---------------

            procedure Add_Loc
              (V : Flow_Graphs.Vertex_Id)
            is
               F : constant Flow_Id := (if CFG_Graph then FA.CFG.Get_Key (V)
                                        else FA.PDG.Get_Key (V));
            begin
               if V /= To and V /= From and F.Kind = Direct_Mapping then
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

         begin --  Vertices_Between_Proof_In_And_Export
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
      begin  --  Path_Leading_To_Proof_In_Dependency
         --  Sanity check that we do not have an empty set.
         pragma Assert (Vertices_To_Cover.Length >= 1);

         Start := FA.Start_Vertex;
         for Vert of Vertices_To_Cover loop
            Path.Union (Vertices_Between_From_And_To
                          (From      => Start,
                           To        => Vert,
                           CFG_Graph => True));

            Start := Vert;
         end loop;

         return Path;
      end Path_Leading_To_Proof_In_Dependency;

   begin  --  Find_Exports_Derived_From_Proof_Ins

      --  If we are dealing with a ghost subprogram then we do NOT
      --  need to perform this check.
      if Is_Ghost_Entity (FA.Analyzed_Entity) then
         return;
      end if;

      for O in FA.Dependency_Map.Iterate loop
         declare
            Output : constant Flow_Id          := Dependency_Maps.Key (O);
            Inputs : constant Flow_Id_Sets.Set := Dependency_Maps.Element (O);
         begin
            if Output /= Null_Flow_Id
              and then Output.Kind in Direct_Mapping | Record_Field
              and then not Is_Ghost_Entity (Get_Direct_Mapping_Id (Output))
            then
               for Input of Inputs loop
                  declare
                     V              : constant Flow_Graphs.Vertex_Id :=
                       Get_Initial_Vertex (FA.PDG, Input);
                     Tracefile      : constant String := Fresh_Trace_File;
                     Vertices_Trail : Vertex_Sets.Set;
                  begin
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.Atr.Element (V).Mode = Mode_Proof
                     then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "export & must not depend " &
                             "on Proof_In &",
                           SRM_Ref   => "6.1.4(18)",
                           N         => Find_Global (FA.Analyzed_Entity,
                                                     Input),
                           F1        => Output,
                           F2        => Input,
                           Kind      => Error_Kind,
                           Tag       => Export_Depends_On_Proof_In);

                        Vertices_Trail := Path_Leading_To_Proof_In_Dependency
                          (From => V,
                           To   => Get_Final_Vertex (FA.PDG, Output));

                        Write_Vertex_Set
                          (FA       => FA,
                           Set      => Vertices_Trail,
                           Filename => Tracefile);
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
         Scop : Entity_Id;
      begin
         Scop := E;
         while Present (Scop) loop

            --  If we reach Standard_Standard then there is no
            --  enclosing package which has state.

            if Scop = Standard_Standard then
               return False;

            --  If we find a body then we need to look if the entity
            --  of the spec has abstract state.

            elsif Ekind (Scop) = E_Package_Body
              and then Present (Abstract_States (Spec_Entity (Scop)))
            then
               return True;

            --  If we find a spec then we look if it has abstract
            --  state.

            elsif Is_Package_Or_Generic_Package (Scop)
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
         end loop;

         --  If we reach this point then there is no enclosing package
         --  which has state.
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
                    (FA   => FA,
                     Msg  => "& needs to be a constituent of " &
                               "some state abstraction",
                     N    => Hidden_State,
                     F1   => Direct_Mapping_Id (Hidden_State),
                     Tag  => Hidden_Unexposed_State,
                     Kind => Medium_Check_Kind);
               end if;

               Next_Entity (Hidden_State);
            end loop;
         end Warn_On_Non_Constant;

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
                 and then Has_Variable_Input (F)
                 and then not All_Constituents.Contains (F)
               then
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "& needs to be a constituent of " &
                               "some state abstraction",
                     N    => Hidden_State,
                     F1   => F,
                     Tag  => Hidden_Unexposed_State,
                     Kind => Medium_Check_Kind);
               end if;

               Next_Entity (Hidden_State);
            end loop;
         end Warn_On_Unexposed_Constant;

      begin
         --  Sanity check that we do have a Refined_State aspect
         pragma Assert (Present (Refined_State_N));

         --  Gather up all constituents mentioned in the Refined_State
         --  aspect.
         DM := Parse_Refined_State (Refined_State_N);
         for State in DM.Iterate loop
            All_Constituents.Union (Dependency_Maps.Element (State));
         end loop;

         --  Warn about hidden unexposed constants with variable input
         --  that lie in the private part.
         Warn_On_Unexposed_Constant (First_Private_Entity (E));

         --  Warn about hidden unexposed constants with variable input
         --  that lie in the body.
         Warn_On_Unexposed_Constant (First_Entity (Body_Entity (E)));
      end Warn_About_Unreferenced_Constants;

   begin  --  Find_Hidden_Unexposed_State

      if not Present (Abstract_States (FA.Spec_Entity))
        and then Enclosing_Package_Has_State (FA.Spec_Entity)
      then
         --  If the package does not have an abstract state aspect and
         --  an enclosing package does introduces a state abstraction
         --  then issue a medium check per hidden state.
         Warn_About_Hidden_States (FA.Spec_Entity);
      end if;

      if Present (Abstract_States (FA.Spec_Entity))
        and then Present (Body_Entity (FA.Spec_Entity))
      then
         --  If the package has an abstract state aspect then issue
         --  high checks for every constant with variable input that
         --  is part of the package's hidden state and is not exposed
         --  through a state abstraction.
         Warn_About_Unreferenced_Constants (FA.Spec_Entity);
      end if;

   end Find_Hidden_Unexposed_State;

   -----------------------------------------
   -- Find_Impossible_To_Initialize_State --
   -----------------------------------------

   procedure Find_Impossible_To_Initialize_State
     (FA : in out Flow_Analysis_Graphs)
   is
      function Initialized_By_Initializes_Aspect return Flow_Id_Sets.Set;
      --  Returns the set of all flow ids that are mentioned in the
      --  package's initializes aspect.

      function Outputs_Of_Procedures return Flow_Id_Sets.Set;
      --  Returns the set of all flow ids that are pure outputs (not
      --  In_Outs) of procedures.

      ---------------------------------------
      -- Initialized_By_Initializes_Aspect --
      ---------------------------------------

      function Initialized_By_Initializes_Aspect return Flow_Id_Sets.Set is
         FS : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         DM : constant Dependency_Maps.Map :=
           Parse_Initializes (FA.Initializes_N, FA.Spec_Entity, FA.S_Scope);
      begin

         for C in DM.Iterate loop
            declare
               The_Out : constant Flow_Id := Dependency_Maps.Key (C);
            begin
               FS.Include (The_Out);
            end;
         end loop;

         return FS;
      end Initialized_By_Initializes_Aspect;

      ---------------------------
      -- Outputs_Of_Procedures --
      ---------------------------

      function Outputs_Of_Procedures return Flow_Id_Sets.Set is
         E    : Entity_Id;
         Scop : constant Flow_Scope := FA.S_Scope;
         FS   : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
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
                               Scope      => Scop,
                               Classwide  => False,
                               Proof_Ins  => Proof_Ins,
                               Reads      => Reads,
                               Writes     => Writes);

                  --  If the Flow_Id is an Output (and not an Input)
                  --  of the procedure then include it to FS.

                  for Write of Writes loop
                     if not Reads.Contains (Change_Variant (Write,
                                                            In_View))
                     then
                        FS.Include (Change_Variant (Write, Normal_Use));
                     end if;
                  end loop;
               end;
            end if;

            Next_Entity (E);
         end loop;

         return FS;
      end Outputs_Of_Procedures;

   begin  --  Find_Impossible_To_Initialize_State

      --  If the package either has no state abstractions, or has
      --  "Abstract_State => null" then there is nothing to do here.

      if not Present (Abstract_States (FA.Spec_Entity))
        or else Is_Null_State
                  (Node (First_Elmt (Abstract_States (FA.Spec_Entity))))
      then
         return;
      end if;

      declare
         State_Elmt : Elmt_Id;
         State      : Entity_Id;

         --  The following is the set of all flow ids that are or can
         --  potentially be initialized.
         Initializable : constant Flow_Id_Sets.Set :=
           Initialized_By_Initializes_Aspect or Outputs_Of_Procedures;
      begin
         State_Elmt := First_Elmt (Abstract_States (FA.Spec_Entity));
         State := Node (State_Elmt);

         while Present (State) loop

            if not Initializable.Contains (Direct_Mapping_Id (State))
              and then not Has_Async_Writers (Direct_Mapping_Id (State))
            then
               --  For every state abstraction that is not mentioned
               --  in an Initializes aspect, is not a pure Output of
               --  any procedure and does not have Async_Writers we
               --  emit a warning.

               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "no procedure exists that can initialize " &
                    "abstract state &",
                  N    => State,
                  F1   => Direct_Mapping_Id (State),
                  Tag  => Impossible_To_Initialize_State,
                  Kind => Warning_Kind);
            end if;

            --  Move on to the next state abstraction
            Next_Elmt (State_Elmt);
            State := Node (State_Elmt);
         end loop;
      end;

   end Find_Impossible_To_Initialize_State;

   ----------------------------
   -- Check_Depends_Contract --
   ----------------------------

   procedure Check_Depends_Contract (FA : in out Flow_Analysis_Graphs) is

      User_Deps   : Dependency_Maps.Map;
      Actual_Deps : Dependency_Maps.Map;

      Depends_Location : constant Node_Id :=
        (if Has_Depends (FA.Analyzed_Entity) then
            Get_Pragma (FA.Analyzed_Entity, Pragma_Depends)
         else
            FA.Analyzed_Entity);

      Params      : Node_Sets.Set;
      --  This set will hold all local parameters of the subprogram

      function Message_Kind  (F : Flow_Id) return Msg_Kind;
      --  Returns the severity of the message that we have to emit.
      --
      --  In the absence of a user-provided Global contract the
      --  user-provided Depends contract is utilized to synthesize the
      --  Globals. In this case and if F is a global variable then the
      --  emitted messages are errors since users of the subprogram
      --  will be assuming wrong Globals.
      --
      --  On the other hand, when there exists a user-provided Global
      --  contract or when F is not a Global variable, emitted
      --  messages are medium checks.

      function Up_Project_Map
        (DM : Dependency_Maps.Map)
         return Dependency_Maps.Map;
      --  Up projects the constituents that are mentioned in DM until
      --  we have visibility of the enclosing state abstractions from
      --  FA.S_Scope.
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
      --     Final DM:
      --       State1 => (State1, State2, G)
      --       State2 => (State2, G)
      --       G      => State2
      --
      --  Notice that the self depence of State1 is an indirect
      --  consequence of the fact that Con2 is not an Output. So there
      --  is an implicit Con2 => Con2 dependence.

      ------------------
      -- Message_Kind --
      ------------------

      function Message_Kind (F : Flow_Id) return Msg_Kind is
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
         States_Written       : Node_Sets.Set       := Node_Sets.Empty_Set;
         Constituents_Written : Node_Sets.Set       := Node_Sets.Empty_Set;
         Up_Projected_Map     : Dependency_Maps.Map :=
           Dependency_Maps.Empty_Map;

      begin  --  Up_Project_Map

         for C in DM.Iterate loop
            declare
               F_Out  : Flow_Id                   :=
                 Dependency_Maps.Key (C);
               F_Deps : constant Flow_Id_Sets.Set :=
                 Dependency_Maps.Element (C);
               AS     : Flow_Id;
            begin
               --  Add output
               if Is_Non_Visible_Constituent (F_Out, FA.S_Scope) then
                  AS := Up_Project_Constituent (F_Out, FA.S_Scope);

                  --  Add closest enclosing abstract state to the map
                  --  (if it is not already in it).
                  if not Up_Projected_Map.Contains (AS) then
                     Up_Projected_Map.Include (AS, Flow_Id_Sets.Empty_Set);
                  end if;

                  --  Taking some notes
                  States_Written.Include (Get_Direct_Mapping_Id (AS));
                  Constituents_Written.Include
                    (Get_Direct_Mapping_Id (F_Out));
                  F_Out := AS;
               else
                  --  Add output as it is
                  Up_Projected_Map.Include (F_Out, Flow_Id_Sets.Empty_Set);
               end if;

               --  Add output's dependencies
               for Dep of F_Deps loop
                  if Is_Non_Visible_Constituent (Dep, FA.S_Scope) then
                     AS := Up_Project_Constituent (Dep, FA.S_Scope);

                     --  Add closest enclosing abstract state
                     Up_Projected_Map (F_Out).Include (AS);
                  else
                     --  Add output as it is
                     Up_Projected_Map (F_Out).Include (Dep);
                  end if;
               end loop;
            end;
         end loop;

         --  If at least one constituent of a state abstraction has
         --  not been written, then the state abstraction also depends
         --  on itself.
         for State of States_Written loop
            declare
               Constit_Elmt : Elmt_Id;
               Constit_Id   : Entity_Id;
               Keep_Going   : Boolean          := True;
               AS           : constant Flow_Id := Direct_Mapping_Id (State);
            begin
               Constit_Elmt := First_Elmt (Refinement_Constituents (State));
               while Present (Constit_Elmt)
                 and then Keep_Going
               loop
                  Constit_Id := Node (Constit_Elmt);

                  if not Constituents_Written.Contains (Constit_Id) then
                     --  Abstract state also depends on itself
                     Up_Projected_Map (AS).Include (AS);

                     --  There is no need to check the rest of the
                     --  constituents.
                     Keep_Going := False;
                  end if;

                  Next_Elmt (Constit_Elmt);
               end loop;
            end;
         end loop;

         return Up_Projected_Map;
      end Up_Project_Map;

   begin  --  Check_Depends_Contract

      if No (FA.Depends_N) then
         --  If the user has not specified a dependency relation we
         --  have no work to do.
         return;
      end if;

      Get_Depends (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Classwide  => False,
                   Depends    => User_Deps);

      --  Populate the Params set
      declare
         E : Entity_Id;
      begin
         E := First_Formal (FA.Analyzed_Entity);
         while Present (E) loop
            Params.Include (E);
            E := Next_Formal (E);
         end loop;
      end;

      if FA.Is_Generative
        and then No (FA.Refined_Depends_N)
        and then Mentions_State_With_Visible_Refinement (FA.Depends_N,
                                                         FA.B_Scope)
      then
         --  Use the abstract states versions of the dependencies
         User_Deps   := Up_Project_Map (User_Deps);
         Actual_Deps := Up_Project_Map (FA.Dependency_Map);
      else
         --  Use the down projected version of the dependencies
         Actual_Deps := FA.Dependency_Map;
      end if;

      if Debug_Trace_Depends then
         Print_Dependency_Map (User_Deps);
         Print_Dependency_Map (Actual_Deps);
      end if;

      --  If the user depends do not include something we have in the
      --  actual depends we will raise an appropriate error. We should
      --  however also sanity check there is nothing in the user
      --  dependencies which is *not* in the actual dependencies.

      for C in User_Deps.Iterate loop
         declare
            F_Out : constant Flow_Id := Dependency_Maps.Key (C);
         begin
            if not Actual_Deps.Contains (F_Out) then
               --  ??? check quotation in errout.ads
               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "incorrect dependency & is not an output of &",
                  N    => Search_Contract (FA.Analyzed_Entity,
                                           Pragma_Depends,
                                           Get_Direct_Mapping_Id (F_Out)),
                  F1   => F_Out,
                  F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag  => Depends_Null,
                  Kind => Medium_Check_Kind);
            end if;
         end;
      end loop;

      --  We go through the actual dependencies because they are
      --  always complete.

      for C in Actual_Deps.Iterate loop
         declare
            F_Out  : constant Flow_Id          := Dependency_Maps.Key (C);
            A_Deps : constant Flow_Id_Sets.Set :=
              Dependency_Maps.Element (C);
            U_Deps : Flow_Id_Sets.Set;

            Missing_Deps : Ordered_Flow_Id_Sets.Set;
            Wrong_Deps   : Ordered_Flow_Id_Sets.Set;

            Proceed_With_Analysis : Boolean := True;
         begin
            if F_Out = Null_Flow_Id then
               --  The null dependency is special: it may not be
               --  present in the user dependency because null => null
               --  would be super tedious to write.
               if User_Deps.Contains (Null_Flow_Id) then
                  U_Deps := User_Deps (Null_Flow_Id);
               else
                  U_Deps := Flow_Id_Sets.Empty_Set;
               end if;
            elsif User_Deps.Contains (F_Out) then
               U_Deps := User_Deps (F_Out);
            elsif F_Out.Kind = Magic_String then
               Global_Required (FA, F_Out);
               Proceed_With_Analysis := False;
            else
               --  If the depends aspect is used to synthesize the
               --  global aspect, then this is message will be an
               --  error instead of a medium check.
               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "expected to see & on the left-hand-side of" &
                    " a dependency relation",
                  N    => Depends_Location,
                  F1   => F_Out,
                  Tag  => Depends_Missing_Clause,
                  Kind => Message_Kind (F_Out));
               U_Deps := Flow_Id_Sets.Empty_Set;
            end if;

            --  If we mention magic strings anywhere, there is no
            --  point in proceeding as the dependency relation
            --  *cannot* be correct.

            if Proceed_With_Analysis then
               for Var of A_Deps loop
                  if Var.Kind = Magic_String then
                     Global_Required (FA, Var);
                     Proceed_With_Analysis := False;
                  end if;
               end loop;
            end if;

            --  If all is still well we now do a consistency check.

            if Proceed_With_Analysis then
               Missing_Deps := To_Ordered_Flow_Id_Set (A_Deps - U_Deps);
               Wrong_Deps   := To_Ordered_Flow_Id_Set (U_Deps - A_Deps);

               for Missing_Var of Missing_Deps loop
                  declare
                     V : constant Flow_Graphs.Vertex_Id :=
                       Get_Initial_Vertex (FA.PDG, Missing_Var);
                  begin
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.Atr.Element (V).Mode = Mode_Proof
                     then
                        null;
                     else
                        --  Something that the user dependency fails to
                        --  mention.
                        if not Is_Variable (Missing_Var) then
                           --  Dealing with a constant
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "& cannot appear in Depends",
                              N    => Depends_Location,
                              F1   => Missing_Var,
                              Tag  => Depends_Null,
                              Kind => Medium_Check_Kind);
                        elsif F_Out = Null_Flow_Id then
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "missing dependency ""null => %""",
                              N    => Depends_Location,
                              F1   => Missing_Var,
                              Tag  => Depends_Null,
                              Kind => Medium_Check_Kind);
                        elsif F_Out = Direct_Mapping_Id
                          (FA.Analyzed_Entity)
                        then
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "missing dependency ""%'Result => %""",
                              N    => Search_Contract
                                        (FA.Analyzed_Entity,
                                         Pragma_Depends,
                                         Get_Direct_Mapping_Id (F_Out)),
                              F1   => F_Out,
                              F2   => Missing_Var,
                              Tag  => Depends_Missing,
                              Kind => Medium_Check_Kind);
                        else
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "missing dependency ""% => %""",
                              N    => Search_Contract
                                        (FA.Analyzed_Entity,
                                         Pragma_Depends,
                                         Get_Direct_Mapping_Id (F_Out)),
                              F1   => F_Out,
                              F2   => Missing_Var,
                              Tag  => Depends_Missing,
                              Kind => Medium_Check_Kind);
                           --  ??? show path
                        end if;
                     end if;
                  end;
               end loop;

               for Wrong_Var of Wrong_Deps loop
                  --  Something the user dependency claims, but does
                  --  not happen in reality.
                  if not Is_Variable (Wrong_Var) then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "& cannot appear in Depends",
                        N    => Depends_Location,
                        F1   => Wrong_Var,
                        Tag  => Depends_Wrong,
                        Kind => Medium_Check_Kind);
                  elsif F_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""null => %""",
                        N    => Depends_Location,
                        F1   => Wrong_Var,
                        Tag  => Depends_Wrong,
                        Kind => Medium_Check_Kind);
                     --  ??? show a path?
                  elsif F_Out = Direct_Mapping_Id
                    (FA.Analyzed_Entity)
                  then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""%'Result => %""",
                        N    => Search_Contract
                                  (FA.Analyzed_Entity,
                                   Pragma_Depends,
                                   Get_Direct_Mapping_Id (F_Out),
                                   Get_Direct_Mapping_Id (Wrong_Var)),
                        F1   => F_Out,
                        F2   => Wrong_Var,
                        Tag  => Depends_Wrong,
                        Kind => Medium_Check_Kind);
                  else
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""% => %""",
                        N    => Search_Contract
                                  (FA.Analyzed_Entity,
                                   Pragma_Depends,
                                   Get_Direct_Mapping_Id (F_Out),
                                   Get_Direct_Mapping_Id (Wrong_Var)),
                        F1   => F_Out,
                        F2   => Wrong_Var,
                        Tag  => Depends_Wrong,
                        Kind => Medium_Check_Kind);
                  end if;
               end loop;
            end if;
         end;
      end loop;
   end Check_Depends_Contract;

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
            F : constant Flow_Id := FA.CFG.Get_Key (V);
         begin
            if (not To.Contains (V)) and F.Kind = Direct_Mapping then
               Path.Include (V);
            end if;
         end Add_Loc;

      begin --  Write_Tracefile
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

   begin  --  Check_Initializes_Contract
      if DM.Is_Empty then
         --  We have nothing to do if DM is empty
         return;
      end if;

      declare
         The_Out             : Flow_Id;
         The_Ins             : Flow_Id_Sets.Set;
         All_Contract_Outs   : Flow_Id_Sets.Set;
         All_Contract_Ins    : Flow_Id_Sets.Set;
         All_Actual_Ins      : Flow_Id_Sets.Set;
         Found_Uninitialized : Boolean := False;
      begin
         --  If we are dealing with a library level package then we
         --  check if everything in the RHS of an initialization_item
         --  has been initialized.
         if Is_Library_Level_Entity (FA.Analyzed_Entity) then
            for C in DM.Iterate loop
               The_Out := Dependency_Maps.Key (C);
               The_Ins := Dependency_Maps.Element (C);

               for G of The_Ins loop
                  if not Is_Initialized_At_Elaboration (G, FA.B_Scope) then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "% must be initialized at elaboration",
                        N    => (if Present (FA.Initializes_N)
                                 then Search_Contract
                                        (FA.Spec_Entity,
                                         Pragma_Initializes,
                                         Get_Direct_Mapping_Id (The_Out),
                                         Get_Direct_Mapping_Id (G))
                                 else FA.Spec_Entity),
                        F1   => G,
                        Kind => High_Check_Kind,
                        Tag  => Uninitialized);
                     Found_Uninitialized := True;
                  end if;
               end loop;
            end loop;
         end if;

         if Found_Uninitialized then
            --  If a variable or state abstraction that has not been
            --  mentioned in an Initializes aspect was found in the
            --  RHS of an initialization_item then we don't do any
            --  further analysis.
            return;
         end if;

         if No (FA.Initializes_N) then
            --  If we are dealing with a generated initializes aspect then we
            --  have no further checks to do.
            return;
         end if;

         for C in DM.Iterate loop
            The_Out := Dependency_Maps.Key (C);
            The_Ins := Dependency_Maps.Element (C);

            All_Contract_Outs := Flow_Id_Sets.Empty_Set;
            All_Contract_Ins  := Flow_Id_Sets.Empty_Set;
            All_Actual_Ins    := Flow_Id_Sets.Empty_Set;

            --  Down project the LHS of an initialization_item
            All_Contract_Outs := Node_Id_Set_To_Flow_Id_Set
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
                  Actual_Out : constant Flow_Id :=
                    Dependency_Maps.Key (O);

                  Actual_Ins : constant Flow_Id_Sets.Set :=
                    Dependency_Maps.Element (O);
               begin
                  if All_Contract_Outs.Contains (Actual_Out) then
                     All_Actual_Ins.Union (Actual_Ins);
                  end if;
               end;
            end loop;

            --  Raise medium checks for actual inputs that are not
            --  mentioned by the Initializes.
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
                        Kind      => Medium_Check_Kind);

                     --  Generate and write the tracefile
                     Write_Tracefile
                       (From      => Get_Initial_Vertex (FA.PDG, Actual_In),
                        To        =>
                          Flow_Id_Set_To_Vertex_Set (All_Contract_Outs),
                        Tracefile => Tracefile);
                  end;
               end if;
            end loop;

            --  Raise medium checks for inputs mentioned in the
            --  Initializes that are not actual inputs.
            for Contract_In of All_Contract_Ins loop
               if not All_Actual_Ins.Contains (Contract_In) then
                  if Is_Variable (Contract_In) then
                     Error_Msg_Flow
                       (FA      => FA,
                        Msg     => "initialization of & does not depend on &",
                        SRM_Ref => "7.1.5(11)",
                        N       => Search_Contract
                                       (FA.Spec_Entity,
                                        Pragma_Initializes,
                                        Get_Direct_Mapping_Id (The_Out)),
                        F1      => The_Out,
                        F2      => Contract_In,
                        Tag     => Initializes_Wrong,
                        Kind    => Medium_Check_Kind);
                  else
                     --  The input is a constant without variable
                     --  input.
                     Error_Msg_Flow
                      (FA   => FA,
                       Msg  => "& cannot appear in Initializes",
                       N    => Search_Contract
                                 (FA.Spec_Entity,
                                  Pragma_Initializes,
                                  Get_Direct_Mapping_Id (The_Out),
                                  Get_Direct_Mapping_Id (Contract_In)),
                       F1   => Contract_In,
                       Tag  => Initializes_Wrong,
                       Kind => Medium_Check_Kind);
                  end if;
               end if;
            end loop;

            --  Raise medium checks for outputs that are constants and
            --  should consequently not be mention in an initializes
            --  aspect.
            for Contract_Out of All_Contract_Outs loop
               if not Is_Variable (Contract_Out) then
                  --  Output is a constant without variable input
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "& cannot appear in Initializes",
                     N    => Search_Contract
                               (FA.Spec_Entity,
                                Pragma_Initializes,
                                Get_Direct_Mapping_Id (Contract_Out)),
                     F1   => Contract_Out,
                     Tag  => Initializes_Wrong,
                     Kind => Medium_Check_Kind);
               end if;
            end loop;
         end loop;
      end;
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
            Vars := Get_Variable_Set
              (N,
               Scope                => FA.B_Scope,
               Local_Constants      => FA.Local_Constants,
               Fold_Functions       => False,
               Use_Computed_Globals => True);

            for Var of Vars loop
               declare
                  Initial_V : constant Flow_Graphs.Vertex_Id :=
                    Get_Initial_Vertex (FA.CFG, Var);

                  Atr       : constant V_Attributes :=
                    FA.Atr.Element (Initial_V);
               begin
                  if not Atr.Is_Import then
                     Error_Msg_Flow
                       (FA         => FA,
                        Msg        => "& is not initialized at " &
                          "subprogram entry",
                        Kind       => High_Check_Kind,
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
            Atr : constant V_Attributes := FA.Atr.Element (V);
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

      function In_Body_Part return Boolean;
      --  @return True iff the Analyzed_Entity is defined in a
      --     package's body.

      ---------------------------------
      -- In_Body_Part return Boolean --
      ---------------------------------

      function In_Body_Part return Boolean is
         Scope : Flow_Scope;
      begin
         --  We start from the spec scope of the analyzed entity and
         --  work our way up until we find either the null flow scope
         --  or a body scope.
         Scope := FA.S_Scope;
         while Present (Scope) loop
            if Scope.Section = Body_Part then
               return True;
            else
               Scope := Get_Enclosing_Flow_Scope (Scope);
            end if;
         end loop;

         return False;
      end In_Body_Part;

   --  Start of processing for Check_Constant_After_Elaboration

   begin
      if Ekind (FA.Analyzed_Entity) = E_Function
        or else In_Body_Part
      then
         --  If we are:
         --     * either dealing with a function
         --     * or the Analyzed_Entity is declared in the body part
         --       of a package
         --  then we do not need to perform this check.
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
      begin
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Proof_Ins  => Proof_Ins,
                      Reads      => Reads,
                      Writes     => Writes);

         for W of Writes loop
            if W.Kind in Direct_Mapping | Record_Field then
               G_Out := Get_Direct_Mapping_Id (W);
               CAE   := Empty;

               if Ekind (G_Out) in E_Variable then
                  CAE := Get_Pragma (G_Out,
                                     Pragma_Constant_After_Elaboration);
               end if;

               if Is_Constant_After_Elaboration (CAE) then
                  if Present (FA.S_Scope) then
                     Error_Msg_Flow
                      (FA   => FA,
                       Msg  => "& must not be an output of publicly"
                                  & " visible procedure &",
                       Kind => High_Check_Kind,
                       N    => FA.Analyzed_Entity,
                       F1   => W,
                       F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                       Tag  => Not_Constant_After_Elaboration);
                  else
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "constant after elaboration & must not be an "
                                   & "output of procedure &",
                        Kind => High_Check_Kind,
                        N    => FA.Analyzed_Entity,
                        F1   => W,
                        F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Tag  => Not_Constant_After_Elaboration);
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
      Found_Volatile_Effect : Boolean := False;

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
               Found_Volatile_Effect := True;

               --  Issue error if dealing with nonvolatile function
               if not Is_Volatile_Function (FA.Analyzed_Entity) then
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "& cannot act as global item of nonvolatile "
                                & "function &",
                     Kind => Error_Kind,
                     N    => FA.Analyzed_Entity,
                     F1   => F,
                     F2   => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag  => Non_Volatile_Function_With_Volatile_Effects);
               end if;
            end if;
         end loop;
      end Check_Set_For_Volatiles;

   begin
      if not (Ekind (FA.Analyzed_Entity) in E_Function | E_Generic_Function)
      then
         --  If we are not dealing with a [generic] function then we have
         --  nothing to do here.
         return;
      end if;

      declare
         Proof_Ins         : Flow_Id_Sets.Set;
         Reads             : Flow_Id_Sets.Set;
         Writes            : Flow_Id_Sets.Set;
         Formal_Parameters : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

         E                 : Entity_Id;
      begin
         --  Populate global sets
         Get_Globals (Subprogram => FA.Analyzed_Entity,
                      Scope      => FA.B_Scope,
                      Classwide  => False,
                      Proof_Ins  => Proof_Ins,
                      Reads      => Reads,
                      Writes     => Writes);

         --  Populate formal parameters set
         E := First_Formal (FA.Spec_Entity);
         while Present (E) loop
            Formal_Parameters.Include (Direct_Mapping_Id (E));
            E := Next_Formal (E);
         end loop;

         --  Check globals and formal parameters for volatiles and emit
         --  messages if needed
         Check_Set_For_Volatiles (Proof_Ins);
         Check_Set_For_Volatiles (Reads);
         Check_Set_For_Volatiles (Writes);
         Check_Set_For_Volatiles (Formal_Parameters);
      end;

      --  Issue warning if dealing with volatile function without volatile
      --  effects.
      if Is_Volatile_Function (FA.Analyzed_Entity)
        and then not Found_Volatile_Effect
      then
         Error_Msg_Flow
           (FA   => FA,
            Msg  => "volatile function & has no volatile effects",
            Kind => Warning_Kind,
            N    => FA.Analyzed_Entity,
            F1   => Direct_Mapping_Id (FA.Analyzed_Entity),
            Tag  => Volatile_Function_Without_Volatile_Effects);
      end if;
   end Check_Function_For_Volatile_Effects;

end Flow.Analysis;
