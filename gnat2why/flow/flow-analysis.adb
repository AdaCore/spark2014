------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2013-2014, Altran UK Limited                 --
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

with Elists;               use Elists;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sem_Util;             use Sem_Util;
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;
with Snames;               use Snames;
with Stand;                use Stand;

with Why;
with Gnat2Why_Args;

with SPARK_Util;           use SPARK_Util;

with Flow.Analysis.Sanity;
with Flow_Debug;           use Flow_Debug;
with Flow_Error_Messages;  use Flow_Error_Messages;
with Flow_Tree_Utility;    use Flow_Tree_Utility;
with Flow_Utility;         use Flow_Utility;

-----------------------------------------------------------------------------
--
--  ??? Important: Please make sure to always use FA.Atr.Element (V)
--  instead of the implicit reference FA.Atr (V), due to finalization
--  issues. See N131-017 for further information.
--
-----------------------------------------------------------------------------

package body Flow.Analysis is

   Debug_Trace_Depends : constant Boolean := False;
   --  Enable this to show the specified and computed dependency relation.

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
   --  Write a trace file for GPS.

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
     with Pre => F.Variant = Normal_Use,
          Post => G.Get_Key
            (Get_Initial_Vertex'Result).Variant in Initial_Value |
                                                   Initial_Grouping;
   --  Returns the vertex id which represents the initial value for F

   function Get_Final_Vertex (G : Flow_Graphs.T;
                              F : Flow_Id)
                              return Flow_Graphs.Vertex_Id
     with Pre => F.Variant = Normal_Use,
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
      if not Set.Is_Empty then
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
           (FA        => FA,
            Msg       => "bug: & contains reference to &, " &
              "but no use can be found",
            N         => FA.Analyzed_Entity,
            F1        => Direct_Mapping_Id (FA.Analyzed_Entity),
            F2        => Var,
            Kind      => Error_Kind);

      else
         pragma Assert (Nkind (First_Use) in N_Subprogram_Call);

         if Gnat2Why_Args.Flow_Advanced_Debug then
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "called subprogram & requires GLOBAL " &
                 "aspect to make state & visible",
               N         => First_Use,
               F1        => Direct_Mapping_Id (Entity (Name (First_Use))),
               F2        => Var,
               Kind      => Error_Kind);
         else
            Error_Msg_Flow
              (FA        => FA,
               Msg       => "called subprogram & requires GLOBAL " &
                 "aspect to make state visible",
               N         => First_Use,
               F1        => Direct_Mapping_Id (Entity (Name (First_Use))),
               Kind      => Error_Kind);
         end if;
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
   begin
      case Ekind (S) is
         when E_Package_Body =>
            Haystack_A := Empty;
            Haystack_B := Get_Pragma (Spec_Entity (S), Pragma_Initializes);

         when E_Package =>
            Haystack_A := Empty;
            Haystack_B := Get_Pragma (S, Pragma_Initializes);

         when others =>
            if Present (Get_Body (S)) then
               Haystack_A := Get_Pragma (Get_Body (S), Pragma_Refined_Global);
            else
               Haystack_A := Empty;
            end if;
            Haystack_B := Get_Pragma (S, Pragma_Global);
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
      raise Program_Error;
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
            if Atr.Variables_Used.Contains (Var_Normal) or
              (not Precise and then
                 To_Entire_Variables (Atr.Variables_Used).Contains
                 (E_Var_Normal))
            then
               Of_Interest := True;
            end if;
         end if;
         if Check_Write then
            if Atr.Variables_Defined.Contains (Var_Normal) or
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
              (FA        => FA,
               Msg       => "& might not be initialized after elaboration " &
                 "of main program &",
               N         => Find_Global (FA.Analyzed_Entity, R),
               F1        => R,
               F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag       => "uninitialized",
               Kind      => Medium_Check_Kind);
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
         Sanity.Check_Aliasing'Access,
         Sanity.Check_Variable_Free_Expressions'Access,
         Sanity.Check_Illegal_Reads'Access,
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
                  when E_Subprogram_Body => (if Refined
                                             then "Refined_Global"
                                             else "Global"),
                  when others => "Initializes");

            SRM_Ref : constant String :=
              (case FA.Kind is
                  when E_Subprogram_Body => "6.1.4(13)",
                  when others            => "7.1.5(12)");

         begin
            if Refined then
               Vars_Known := To_Entire_Variables (FA.All_Vars);
            else
               case FA.Kind is
                  when E_Subprogram_Body =>
                     Vars_Known := Flow_Id_Sets.Empty_Set;

                     --  We need to assemble the variables known from
                     --  the spec: these are parameters and globals.
                     declare
                        E                   : Entity_Id;
                        Tmp_A, Tmp_B, Tmp_C : Flow_Id_Sets.Set;
                     begin
                        E := First_Formal (FA.Spec_Node);
                        while Present (E) loop
                           Vars_Known.Include (Direct_Mapping_Id (E));
                           E := Next_Formal (E);
                        end loop;

                        Get_Globals (Subprogram => FA.Spec_Node,
                                     Scope      => FA.S_Scope,
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
                     Vars_Known := To_Flow_Id_Set
                       (Down_Project (To_Node_Set (To_Entire_Variables
                                                     (FA.Visible_Vars)),
                                      FA.S_Scope));
               end case;
            end if;

            for Expr of Get_Postcondition_Expressions (FA.Spec_Node,
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
                       (FA        => FA,
                        Msg       => "& must be listed in the " &
                          Aspect_To_Fix &
                          " aspect of &",
                        SRM_Ref   => SRM_Ref,
                        N         => First_Variable_Use
                          (N       => Expr,
                           FA      => FA,
                           Scope   => FA.B_Scope,
                           Var     => Var,
                           Precise => False),
                        F1        => Entire_Variable (Var),
                        F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
                        Kind      => Error_Kind);
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
                       (FA        => FA,
                        Msg       => "& must be initialized at elaboration",
                        N         => First_Variable_Use (N       => Expr,
                                                         FA      => FA,
                                                         Scope   => FA.B_Scope,
                                                         Var     => Var,
                                                         Precise => False),
                        F1        => Entire_Variable (Var),
                        Kind      => Error_Kind);
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
                    (FA        => FA,
                     Msg       => "& is not modified, could be INPUT",
                     N         => Find_Global (FA.Analyzed_Entity, F_Final),
                     F1        => Entire_Variable (F_Final),
                     Tag       => "inout_only_read",
                     Kind      => Warning_Kind,
                     Vertex    => V);
               else
                  Error_Msg_Flow
                    (FA        => FA,
                     Msg       => "& is not modified, could be IN",
                     N         => Error_Location (FA.PDG, FA.Atr, V),
                     F1        => Entire_Variable (F_Final),
                     Tag       => "inout_only_read",
                     Kind      => Warning_Kind,
                     Vertex    => V);
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
      --  Checks if the given vertex V is a final-use vertex or useful for
      --  proof.

      Suppressed_Entire_Ids : Flow_Id_Sets.Set;
      --  Entire variables appearing in a "null => Blah" dependency
      --  relation, for these we suppress the ineffective import warning.

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

      EV_Unused      : Flow_Id_Sets.Set;
      EV_Ineffective : Flow_Id_Sets.Set;

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
            if Key.Variant = Initial_Value and
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
                        if FA.PDG.Get_Key (Final_V).Variant /= Final_Value or
                          FA.PDG.In_Neighbour_Count (Final_V) > 1
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
               --  We have an unused global, we need to give the error on
               --  the subprogram, instead of the global. In generative
               --  mode we don't produce this warning.
               if not FA.Is_Generative then
                  Error_Msg_Flow
                    (FA      => FA,
                     Msg     => "unused global &",
                     N       => Find_Global (FA.Analyzed_Entity, F),
                     F1      => F,
                     Tag     => "unused",
                     Kind    => Warning_Kind);
               end if;
            else
               --  ??? distinguish between variables and parameters
               Error_Msg_Flow
                 (FA      => FA,
                  Msg     => "unused variable &",
                  N       => Error_Location (FA.PDG, FA.Atr, V),
                  F1      => F,
                  Tag     => "unused",
                  Kind    => Warning_Kind);
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
               if FA.Kind = E_Subprogram_Body and then
                 not FA.Is_Generative
               then
                  Error_Msg_Flow
                    (FA      => FA,
                     Msg     =>
                       (if FA.B_Scope.Section /= Body_Part
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
                     N       => Find_Global (FA.Analyzed_Entity, F),
                     F1      => F,
                     F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
                     Tag     => "unused_initial_value",
                     Kind    => Warning_Kind);
               end if;
            else
               Error_Msg_Flow
                 (FA      => FA,
                  Msg     => "unused initial value of &",
                  --  ??? find_import
                  N       => Error_Location (FA.PDG, FA.Atr, V),
                  F1      => F,
                  F2      => Direct_Mapping_Id (FA.Analyzed_Entity),
                  Tag     => "unused_initial_value",
                  Kind    => Warning_Kind);
            end if;
         end;
      end loop;
   end Find_Ineffective_Imports_And_Unused_Objects;

   ---------------------------------
   -- Find_Ineffective_Statements --
   ---------------------------------

   procedure Find_Ineffective_Statements (FA : in out Flow_Analysis_Graphs) is

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean;
      --  Checks if the given vertex V is a final-use vertex that is
      --  also an export.

      function Is_Final_Use_Unreferenced (V : Flow_Graphs.Vertex_Id)
                                          return Boolean;
      --  Checks if the given vertex V is a final-use vertex that
      --  corresponds to a variable that is mentioned in a pragma
      --  Unreferenced.

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id)
                                 return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id)
                            return Boolean;
      --  Checks if from the given vertex V it is impossible to reach the
      --  end vertex.

      function Other_Fields_Are_Ineffective (V : Flow_Graphs.Vertex_Id)
                                             return Boolean;
      --  This function returns True if V corresponds to an assignment
      --  to a record field that has been introduced by a record split
      --  and the rest of the fields are ineffective.

      function Find_Masking_Code
        (Ineffective_Statement : Flow_Graphs.Vertex_Id)
         return Vertex_Sets.Set;
      --  Find out why a given vertex is ineffective. A vertex is
      --  ineffective if the variable(s) defined by it are re-defined
      --  on all paths leading from it without being used. Thus all
      --  reachable vertices which also define at least one variable
      --  of that set (and do not use it), render the vertex
      --  ineffective.

      function Skip_Any_Conversions (N : Node_Or_Entity_Id)
                                     return Node_Or_Entity_Id;
      --  Skips any conversions (unchecked or otherwise) and jumps to
      --  the actual object.

      -----------------------------
      -- Is_Final_Use_Any_Export --
      -----------------------------

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value and then
           FA.Atr.Element (V).Is_Export;
      end Is_Final_Use_Any_Export;

      -------------------------------
      -- Is_Final_Use_Unreferenced --
      -------------------------------

      function Is_Final_Use_Unreferenced (V : Flow_Graphs.Vertex_Id)
                                          return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value and then
           FA.Unreferenced_Vars.Contains
             (Get_Direct_Mapping_Id (Change_Variant
                                       (FA.PDG.Get_Key (V), Normal_Use)));
      end Is_Final_Use_Unreferenced;

      ----------------------
      -- Is_Any_Final_Use --
      ----------------------

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id)
                                 return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value;
      end Is_Any_Final_Use;

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

      -----------------
      -- Is_Dead_End --
      -----------------

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id)
                            return Boolean
      is
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
            Tag       : constant String       := "ineffective";
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
                 (if FA.Kind in E_Package | E_Package_Body and then
                    not Present (FA.Initializes_N)
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
                 (not FA.Lead_To_Abnormal_Termination.Contains (V) or else
                    FA.CFG.Out_Neighbour_Count (V) =
                      FA.Lead_To_Abnormal_Termination.Element (V)) and then

                 --  Suppression for vertices that correspond to
                 --  an assignment to a record field, that comes
                 --  from a record split, while the rest of the
                 --  fields are not ineffective.
                 Other_Fields_Are_Ineffective (V)
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
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "initialization has no effect",
                           N         => Error_Location (FA.PDG, FA.Atr, V),
                           Tag       => Tag,
                           Kind      => Warning_Kind,
                           Vertex    => V);
                     end if;
                     --  This warning is ignored for local constants.

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

   procedure Find_Dead_Code (FA : in out Flow_Analysis_Graphs)
   is
      Dead_Code : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Flag the given node as "live" and continue traversal if
      --  appropriate.

      procedure Flag_Live (V  : Flow_Graphs.Vertex_Id;
                           TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         Atr : constant V_Attributes := FA.Atr.Element (V);
      begin
         Dead_Code.Exclude (V);

         if Atr.Execution /= Normal_Execution then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Flag_Live;

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
                  Visitor       => Flag_Live'Access);

      --  Anything remaining is dead
      for V of Dead_Code loop
         declare
            A      : constant V_Attributes := FA.Atr.Element (V);
         begin
            Error_Msg_Flow (FA        => FA,
                            Msg       => "this statement is never reached",
                            N         => A.Error_Location,
                            Tag       => "dead_code",
                            Kind      => Warning_Kind,
                            Vertex    => V);
         end;
      end loop;
   end Find_Dead_Code;

   -----------------------------------------
   -- Find_Use_Of_Uninitialized_Variables --
   -----------------------------------------

   procedure Find_Use_Of_Uninitialized_Variables
     (FA : in out Flow_Analysis_Graphs)
   is
      Tracefile : Unbounded_String;

      procedure Mark_Definition_Free_Path
        (From      : Flow_Graphs.Vertex_Id;
         To        : Flow_Graphs.Vertex_Id;
         Var       : Flow_Id;
         V_Allowed : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
      --  Write a trace file for the error message at E_Loc with the
      --  given Tag. The trace will mark the path From -> To which
      --  does not define Var. If V_Allowed is set, then the path that
      --  we return is allowed to contain V_Allowed even if V_Allowed
      --  does set Var.

      procedure Might_Be_Defined_In_Other_Path
        (V_Initial : Flow_Graphs.Vertex_Id;
         V_Use     : Flow_Graphs.Vertex_Id;
         Found     : out Boolean;
         V_Error   : out Flow_Graphs.Vertex_Id);
      --  Sets Found when the variable corresponding to V_Initial is
      --  defined on a path that lead to V_Use. V_Error is the vertex
      --  where the message should be emitted.

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

         procedure Add_Loc (V : Flow_Graphs.Vertex_Id)
         is
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

         --  A little sanity check can't hurt.
         pragma Assert (Path_Found);

         Write_Vertex_Set (FA       => FA,
                           Set      => Path,
                           Filename => To_String (Tracefile));
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
              and then Ekind (Etype (The_Var.Node)) in Type_Kind
              and then Has_Array_Type (Etype (The_Var.Node)))
           or else
           (The_Var.Kind = Record_Field
              and then The_Var.Facet = Normal_Part
              and then Ekind (Etype (The_Var.Component.Last_Element))
                         in Type_Kind
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

         if (not Found) and then Use_Vertex_Points_To_Itself then
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

   begin --  Find_Use_Of_Uninitialized_Variables
      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop

         --  We loop through all vertices, finding the ones that
         --  represent initial values that are not initialized.

         declare
            Key_I : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Atr_I : constant V_Attributes := FA.Atr.Element (V_Initial);
         begin
            if Key_I.Variant = Initial_Value
              and then not Atr_I.Is_Initialized
            then

               --  V_Initial is a vertex of an uninitialized initial value
               --  Key_I     is its flow_id
               --  Atr_I     are its attributes

               --  We now look at all its out neighbours in the PDG
               --  (these are vertices using (or depending on) this
               --  uninitialized initial value).

               for V_Use of FA.PDG.Get_Collection (V_Initial,
                                                   Flow_Graphs.Out_Neighbours)
               loop
                  declare
                     Key_U : constant Flow_Id      := FA.PDG.Get_Key (V_Use);
                     Atr_U : constant V_Attributes := FA.Atr.Element (V_Use);

                     Action : constant String := (if Has_Async_Readers (Key_I)
                                                  then "written"
                                                  else "initialized");

                     Defined_Elsewhere : Boolean;
                     V_Error           : Flow_Graphs.Vertex_Id;
                  begin

                     --  Get a name for a new trace file
                     Tracefile := To_Unbounded_String (Fresh_Trace_File);

                     --  V_Use is a vertex that depends on V_Initial
                     --  Key_U is its flow_id
                     --  Atr_U are its attributes

                     --  There are a number of places an uninitialized
                     --  value might be used, we issue slightly
                     --  different error messages depending on what
                     --  V_Use represents.

                     Might_Be_Defined_In_Other_Path
                       (V_Initial => V_Initial,
                        V_Use     => V_Use,
                        Found     => Defined_Elsewhere,
                        V_Error   => V_Error);

                     if Key_U.Variant = Final_Value then

                        --  This is a final value vertex; this
                        --  suggests there is a path in the CFG that
                        --  never sets the variable.

                        if not (Is_Abstract_State (Key_U) and then
                                  Ekind (FA.Analyzed_Entity) in E_Package |
                                                                E_Package_Body)
                        then

                           --  If the final vertex corresponds to a
                           --  state abstraction and we are analyzing
                           --  a package then we do not consider this
                           --  to be an issue as state abstractions do
                           --  not have to always be initialized after
                           --  a package's elaboration.

                           if Atr_U.Is_Global then
                              if Defined_Elsewhere then
                                 Error_Msg_Flow
                                   (FA        => FA,
                                    Tracefile => To_String (Tracefile),
                                    Msg       => "& might not be " & Action,
                                    N         => Find_Global
                                      (FA.Analyzed_Entity, Key_I),
                                    F1        => Key_I,
                                    Tag       => "uninitialized",
                                    Kind      => Medium_Check_Kind,
                                    Vertex    => V_Use);
                              else
                                 Error_Msg_Flow
                                   (FA        => FA,
                                    Tracefile => To_String (Tracefile),
                                    Msg       => "& is not " & Action,
                                    N         => Find_Global
                                      (FA.Analyzed_Entity, Key_I),
                                    F1        => Key_I,
                                    Tag       => "uninitialized",
                                    Kind      => High_Check_Kind,
                                    Vertex    => V_Use);
                              end if;
                              Mark_Definition_Free_Path
                                (From => FA.Start_Vertex,
                                 To   => FA.Helper_End_Vertex,
                                 Var  => Change_Variant (Key_I, Normal_Use));

                           elsif Atr_U.Is_Function_Return then

                              --  This is actually a totally different
                              --  error. It means we have a path where we
                              --  do not return from the function.

                              if not FA.Last_Statement_Is_Raise then

                                 --  We only issue this error when the
                                 --  last statement is not a raise
                                 --  statement.

                                 Error_Msg_Flow
                                   (FA        => FA,
                                    Tracefile => To_String (Tracefile),
                                    Msg       =>
                                      (if Defined_Elsewhere
                                       then "possibly missing return "
                                               & "statement in &"
                                       else "missing return "
                                               & "statement in &"),
                                    N         =>
                                      Error_Location (FA.PDG,
                                                      FA.Atr,
                                                      FA.Start_Vertex),
                                    F1        => Direct_Mapping_Id
                                      (FA.Analyzed_Entity),
                                    Tag       => "missing_return",
                                    Kind      => (if Defined_Elsewhere
                                                  then Warning_Kind
                                                  else Error_Kind),
                                    Vertex    => V_Use);
                                 Mark_Definition_Free_Path
                                   (From => FA.Start_Vertex,
                                    To   => FA.Helper_End_Vertex,
                                    Var  => Change_Variant (Key_I,
                                                            Normal_Use));
                              end if;

                           elsif Atr_U.Is_Export then

                              --  As we don't have a global, but an
                              --  export, it means we must be dealing
                              --  with a parameter.

                              if Defined_Elsewhere then
                                 Error_Msg_Flow
                                   (FA        => FA,
                                    Tracefile => To_String (Tracefile),
                                    Msg       => "& might not be " & Action &
                                      " in &",
                                    N         => First_Variable_Use
                                      (N        =>  Error_Location (FA.PDG,
                                                                    FA.Atr,
                                                                    V_Error),
                                       FA       => FA,
                                       Scope    => FA.B_Scope,
                                       Var      => Key_I,
                                       Precise  => True,
                                       Targeted => True),
                                    F1        => Key_I,
                                    F2        => Direct_Mapping_Id
                                      (FA.Analyzed_Entity),
                                    Tag       => "uninitialized",
                                    Kind      => Medium_Check_Kind,
                                    Vertex    => V_Use);
                              else
                                 Error_Msg_Flow
                                   (FA        => FA,
                                    Tracefile => To_String (Tracefile),
                                    Msg       => "& is not " & Action &
                                      " in &",
                                    N         => First_Variable_Use
                                      (N        =>  Error_Location (FA.PDG,
                                                                    FA.Atr,
                                                                    V_Error),
                                       FA       => FA,
                                       Scope    => FA.B_Scope,
                                       Var      => Key_I,
                                       Precise  => True,
                                       Targeted => True),
                                    F1        => Key_I,
                                    F2        => Direct_Mapping_Id
                                      (FA.Analyzed_Entity),
                                    Tag       => "uninitialized",
                                    Kind      => High_Check_Kind,
                                    Vertex    => V_Use);
                              end if;
                              Mark_Definition_Free_Path
                                (From      => FA.Start_Vertex,
                                 To        => V_Error,
                                 Var       => Change_Variant (Key_I,
                                                              Normal_Use),
                                 V_Allowed => V_Use);

                           else

                              --  We are dealing with a local variable,
                              --  so we don't care if there is a path
                              --  where it is not set.

                              null;
                           end if;

                        end if;

                     else

                        --  V_Use is not a final vertex.

                        if Defined_Elsewhere then
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => To_String (Tracefile),
                              Msg       => "& might not be " & Action,
                              N         => First_Variable_Use
                                (N        =>  Error_Location (FA.PDG,
                                                              FA.Atr,
                                                              V_Error),
                                 FA       => FA,
                                 Scope    => FA.B_Scope,
                                 Var      => Key_I,
                                 Precise  => True,
                                 Targeted => True),
                              F1        => Key_I,
                              Tag       => "uninitialized",
                              Kind      => Medium_Check_Kind,
                              Vertex    => V_Use);
                        else
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => To_String (Tracefile),
                              Msg       => "& is not " & Action,
                              N         => First_Variable_Use
                                (N        =>  Error_Location (FA.PDG,
                                                              FA.Atr,
                                                              V_Error),
                                 FA       => FA,
                                 Scope    => FA.B_Scope,
                                 Var      => Key_I,
                                 Precise  => True,
                                 Targeted => True),
                              F1        => Key_I,
                              Tag       => "uninitialized",
                              Kind      => High_Check_Kind,
                              Vertex    => V_Use);
                        end if;
                        Mark_Definition_Free_Path
                          (From      => FA.Start_Vertex,
                           To        => V_Error,
                           Var       => Change_Variant (Key_I, Normal_Use),
                           V_Allowed => V_Use);

                     end if;
                  end;
               end loop;
            end if;
         end;
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
                          (FA        => FA,
                           Msg       => "stable",
                           N         => Error_Location (FA.PDG,
                                                        FA.Atr,
                                                        N_Loop),
                           Tag       => "stable",
                           Kind      => Warning_Kind,
                           Vertex    => N_Loop);

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
      for O in FA.Dependency_Map.Iterate loop
         declare
            Output : constant Flow_Id          := Dependency_Maps.Key (O);
            Inputs : constant Flow_Id_Sets.Set := Dependency_Maps.Element (O);
         begin
            if Output = Null_Flow_Id then
               null;
            else
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
                           SRM_Ref   => "6.1.4(17)",
                           N         => Find_Global (FA.Analyzed_Entity,
                                                     Input),
                           F1        => Output,
                           F2        => Input,
                           Kind      => Error_Kind,
                           Tag       => "export_depends_on_proof_in");

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
      --  Issues one warning per hidden state found in package E

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

            elsif Ekind (Scop) in E_Generic_Package | E_Package
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
         --  Goes through a list of entities and issues warnings for
         --  any non-constant variables.

         --------------------------
         -- Warn_On_Non_Constant --
         --------------------------

         procedure Warn_On_Non_Constant (First_Ent : Entity_Id) is
            Hidden_State : Entity_Id;
         begin
            Hidden_State := First_Ent;
            while Present (Hidden_State) loop
               if Ekind (Hidden_State) in E_Variable
                 and then not Is_Constant_Object (Hidden_State)
               then
                  Error_Msg_Flow
                    (FA   => FA,
                     Msg  => "& needs to be a constituent of " &
                       "some state abstraction",
                     N    => Hidden_State,
                     F1   => Direct_Mapping_Id (Hidden_State),
                     Tag  => "hidden_unexposed_state",
                     Kind => Medium_Check_Kind);
               end if;

               Next_Entity (Hidden_State);
            end loop;
         end Warn_On_Non_Constant;

      begin
         --  Warn about hidden state that lies in the private part
         Warn_On_Non_Constant (First_Private_Entity (E));

         --  Warn about hidden state that lies in the body
         if Present (Body_Entity (E)) then
            Warn_On_Non_Constant (First_Entity (Body_Entity (E)));
         end if;
      end Warn_About_Hidden_States;

   begin
      --  If the package has state abstraction then there is nothing
      --  to do here.

      if Present (Abstract_States (FA.Spec_Node)) then
         return;
      end if;

      --  If there is no enclosing package that introduces a state
      --  abstraction then the is nothing to do here.

      if not Enclosing_Package_Has_State (FA.Spec_Node) then
         return;
      end if;

      --  Issue one message per hidden state
      Warn_About_Hidden_States (FA.Spec_Node);

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
           (if Present (FA.Initializes_N)
            then Parse_Initializes (FA.Initializes_N)
            else Dependency_Maps.Empty_Map);
      begin
         --  If there is no Initializes aspect then we return an empty
         --  set.

         if not Present (FA.Initializes_N) then
            return FS;
         end if;

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
         E := First_Entity (FA.Spec_Node);
         while Present (E) loop
            if Ekind (E) = E_Procedure then
               declare
                  Proof_Ins : Flow_Id_Sets.Set;
                  Reads     : Flow_Id_Sets.Set;
                  Writes    : Flow_Id_Sets.Set;
               begin
                  Get_Globals (Subprogram => E,
                               Scope      => Scop,
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

   begin
      --  If the package either has no state abstractions, or has
      --  "Abstract_State => null" then there is nothing to do here.

      if not Present (Abstract_States (FA.Spec_Node))
        or else Is_Null_State
                  (Node (First_Elmt (Abstract_States (FA.Spec_Node))))
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
         State_Elmt := First_Elmt (Abstract_States (FA.Spec_Node));
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
                  Tag  => "impossible_to_initialize_state",
                  Kind => Warning_Kind);
            end if;

            --  Move on to the next state abstraction
            Next_Elmt (State_Elmt);
            State := Node (State_Elmt);
         end loop;
      end;

   end Find_Impossible_To_Initialize_State;

   ---------------------
   -- Check_Contracts --
   ---------------------

   procedure Check_Contracts (FA : in out Flow_Analysis_Graphs) is

      function Find_Export
        (E  : Entity_Id;
         E2 : Entity_Id := Empty)
         return Node_Id;
      --  Looks through the depends aspect on FA.Analyzed_Entity and
      --  returns the node which represents E in the dependency for E.
      --  If E2 is present then we return the node which represents E2
      --  on the list of entities that E depends on. If none can be
      --  found, returns FA.Analyzed_Entity as a fallback.

      -----------------
      -- Find_Export --
      -----------------

      function Find_Export
        (E  : Entity_Id;
         E2 : Entity_Id := Empty)
         return Node_Id
      is
         Depends_Contract : Node_Id;
         Needle           : Node_Id := Empty;

         function Proc (N : Node_Id) return Traverse_Result;
         --  Searches dependency aspect for export E and sets needle
         --  to the node, if found.

         function Proc (N : Node_Id) return Traverse_Result is
            Tmp, Tmp2 : Node_Id;
            O, I      : Entity_Id;
         begin
            case Nkind (N) is
               when N_Component_Association =>
                  Tmp := First (Choices (N));
                  while Present (Tmp) loop
                     case Nkind (Tmp) is
                        when N_Attribute_Reference =>
                           O := Entity (Prefix (Tmp));
                        when N_Identifier | N_Expanded_Name =>
                           O := Entity (Tmp);
                        when N_Null | N_Aggregate =>
                           O := Empty;
                        when others =>
                           raise Program_Error;
                     end case;
                     if O = E then
                        Needle := Tmp;
                        if E2 = Empty then
                           return Abandon;
                        end if;

                        --  Look for specific input E2 of export E
                        Tmp2 := Expression (Parent (Tmp));

                        case Nkind (Tmp2) is
                           when N_Attribute_Reference =>
                              I := Entity (Prefix (Tmp2));
                           when N_Identifier | N_Expanded_Name =>
                              I := Entity (Tmp2);
                           when N_Null =>
                              I := Empty;
                           when N_Aggregate =>
                              Tmp2 := First (Expressions (Tmp2));

                              while Present (Tmp2) loop
                                 case Nkind (Tmp2) is
                                    when N_Attribute_Reference =>
                                       I := Entity (Prefix (Tmp2));
                                    when N_Identifier | N_Expanded_Name =>
                                       I := Entity (Tmp2);
                                    when N_Null | N_Aggregate =>
                                       I := Empty;
                                    when others =>
                                       raise Program_Error;
                                 end case;
                                 if I = E2 then
                                    Needle := Tmp2;
                                    return Abandon;
                                 end if;
                                 Tmp2 := Next (Tmp2);
                              end loop;
                           when others =>
                              raise Program_Error;
                        end case;

                        if I = E2 then
                           Needle := Tmp2;
                           return Abandon;
                        end if;

                     end if;
                     Tmp := Next (Tmp);
                  end loop;
                  return Skip;
               when others =>
                  null;
            end case;
            return OK;
         end Proc;

         procedure Find_Export_Internal is new Traverse_Proc (Proc);

      begin
         if Present (FA.Refined_Depends_N) then
            Depends_Contract := FA.Refined_Depends_N;
         elsif Present (FA.Depends_N) then
            Depends_Contract := FA.Depends_N;
         else
            return FA.Analyzed_Entity;
         end if;

         Find_Export_Internal (Depends_Contract);
         if Present (Needle) then
            return Needle;
         else
            return FA.Analyzed_Entity;
         end if;
      end Find_Export;

      User_Deps   : Dependency_Maps.Map;
      Actual_Deps : Dependency_Maps.Map;

      Depends_Location : constant Node_Id :=
        (if Has_Depends (FA.Analyzed_Entity) then
            Get_Pragma (FA.Analyzed_Entity, Pragma_Depends)
         else
            FA.Analyzed_Entity);

   begin --  Check_Contracts

      if No (FA.Depends_N) then
         --  If the user has not specified a dependency relation we have no
         --  work to do.
         return;
      end if;

      Get_Depends (Subprogram => FA.Analyzed_Entity,
                   Scope      => FA.B_Scope,
                   Depends    => User_Deps);

      Actual_Deps := FA.Dependency_Map;

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
                  Msg  => "missing dependency ""null => #""",
                  N    => Depends_Location,
                  F1   => F_Out,
                  Tag  => "depends_null",
                  Kind => Medium_Check_Kind);
            end if;
         end;
      end loop;

      --  We go through the actual dependencies because they are
      --  always complete.

      for C in Actual_Deps.Iterate loop
         declare
            F_Out  : constant Flow_Id          := Dependency_Maps.Key (C);
            A_Deps : constant Flow_Id_Sets.Set := Dependency_Maps.Element (C);
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
               --  ??? legality error, should be moved to frontend;
               --  ??? possibly raise exception here
               Error_Msg_Flow
                 (FA   => FA,
                  Msg  => "expected to see & on the left-hand-side of" &
                    " a dependency relation",
                  N    => Depends_Location,
                  F1   => F_Out,
                  Tag  => "depends_missing_clause",
                  Kind => High_Check_Kind);
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
                        if F_Out = Null_Flow_Id then
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "missing dependency ""null => #""",
                              N    => Depends_Location,
                              F1   => Missing_Var,
                              Tag  => "depends_null",
                              Kind => Medium_Check_Kind);
                        elsif F_Out = Direct_Mapping_Id
                          (FA.Analyzed_Entity)
                        then
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  =>
                                "missing dependency ""#'Result => #""",
                              N    => Find_Export
                                (Get_Direct_Mapping_Id (F_Out)),
                              F1   => F_Out,
                              F2   => Missing_Var,
                              Tag  => "depends_missing",
                              Kind => Medium_Check_Kind);
                        else
                           Error_Msg_Flow
                             (FA   => FA,
                              Msg  => "missing dependency ""# => #""",
                              N    => Find_Export
                                (Get_Direct_Mapping_Id (F_Out)),
                              F1   => F_Out,
                              F2   => Missing_Var,
                              Tag  => "depends_missing",
                              Kind => Medium_Check_Kind);
                           --  ??? show path
                        end if;
                     end if;
                  end;
               end loop;

               for Wrong_Var of Wrong_Deps loop
                  --  Something the user dependency claims, but does
                  --  not happen in reality.
                  if F_Out = Null_Flow_Id then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""null => #""",
                        N    => Depends_Location,
                        F1   => Wrong_Var,
                        Tag  => "depends_wrong",
                        Kind => Medium_Check_Kind);
                     --  ??? show a path?
                  elsif F_Out = Direct_Mapping_Id
                    (FA.Analyzed_Entity)
                  then
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""#'Result => #""",
                        N    => Find_Export
                          (Get_Direct_Mapping_Id (F_Out),
                           Get_Direct_Mapping_Id (Wrong_Var)),
                        F1   => F_Out,
                        F2   => Wrong_Var,
                        Tag  => "depends_wrong",
                        Kind => Medium_Check_Kind);
                  else
                     Error_Msg_Flow
                       (FA   => FA,
                        Msg  => "incorrect dependency ""# => #""",
                        N    => Find_Export
                          (Get_Direct_Mapping_Id (F_Out),
                           Get_Direct_Mapping_Id (Wrong_Var)),
                        F1   => F_Out,
                        F2   => Wrong_Var,
                        Tag  => "depends_wrong",
                        Kind => Medium_Check_Kind);
                  end if;
               end loop;

            end if;

         end;
      end loop;
   end Check_Contracts;

   --------------------------------
   -- Check_Initializes_Contract --
   --------------------------------

   procedure Check_Initializes_Contract (FA : in out Flow_Analysis_Graphs) is

      function Find_Entity
        (E    : Entity_Id;
         E_In : Entity_Id := Empty) return Node_Id;
      --  Looks through the initializes aspect on FA.Analyzed_Entity
      --  and returns the node which represents E in the
      --  initializes_item. If E_In is not Empty then we look at the
      --  right hand side of an initializes_item. Otherwise, by
      --  default, we look at the left hand side. If no node can be
      --  found, we return FA.Initializes_N as a fallback.

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

      -----------------
      -- Find_Entity --
      -----------------

      function Find_Entity
        (E    : Entity_Id;
         E_In : Entity_Id := Empty) return Node_Id
      is
         Initializes_Contract : constant Node_Id := FA.Initializes_N;
         Needle               : Node_Id := Empty;

         function Proc (N : Node_Id) return Traverse_Result;
         --  Searches initializes aspect for export E and sets needle
         --  to the node, if found.

         function Proc (N : Node_Id) return Traverse_Result is
            Tmp : Node_Id;
         begin
            case Nkind (N) is
               when N_Component_Association =>
                  Tmp := First (Choices (N));

                  while Present (Tmp) loop
                     if Entity (Tmp) = E then
                        if not Present (E_In) then
                           Needle := Tmp;
                           return Abandon;
                        else
                           Tmp := Expression (N);

                           case Nkind (Tmp) is
                              when N_Aggregate =>
                                 Tmp := First (Expressions (Tmp));

                                 while Present (Tmp) loop
                                    if Entity (Tmp) = E_In then
                                       Needle := Tmp;
                                       return Abandon;
                                    end if;

                                    Tmp := Next (Tmp);
                                 end loop;

                                 return Skip;

                              when others =>
                                 Needle := Tmp;
                                 return Abandon;
                           end case;
                        end if;
                     end if;

                     Tmp := Next (Tmp);
                  end loop;

                  return Skip;

               when others =>
                  null;
            end case;

            return OK;
         end Proc;

         procedure Find_Export_Internal is new Traverse_Proc (Proc);

      begin
         Find_Export_Internal (Initializes_Contract);
         if Present (Needle) then
            return Needle;
         else
            return Initializes_Contract;
         end if;
      end Find_Entity;

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

         procedure Add_Loc
           (V : Flow_Graphs.Vertex_Id);
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

         procedure Add_Loc
           (V : Flow_Graphs.Vertex_Id)
         is
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

   begin  --  Check_Initializes_Contract
      if not Present (FA.Initializes_N)
        or else not Is_Library_Level_Entity (FA.Analyzed_Entity)
      then
         --  If there is no Initializes contract or if we are not analyzing
         --  a library level entity then we have nothing to do.
         return;
      end if;

      declare
         DM                  : constant Dependency_Maps.Map :=
           Parse_Initializes (FA.Initializes_N);

         The_Out             : Flow_Id;
         The_Ins             : Flow_Id_Sets.Set;
         All_Contract_Outs   : Flow_Id_Sets.Set;
         All_Contract_Ins    : Flow_Id_Sets.Set;
         All_Actual_Ins      : Flow_Id_Sets.Set;
         Found_Uninitialized : Boolean := False;
      begin
         --  Check if everything in the RHS of an initialization_item
         --  has been initialized.
         for C in DM.Iterate loop
            The_Out := Dependency_Maps.Key (C);
            The_Ins := Dependency_Maps.Element (C);

            for G of The_Ins loop
               if not Is_Initialized_At_Elaboration (G, FA.B_Scope) then
                  Error_Msg_Flow
                    (FA        => FA,
                     Msg       => "# must be initialized at elaboration",
                     N         => Find_Entity
                       (E    => Get_Direct_Mapping_Id (The_Out),
                        E_In => Get_Direct_Mapping_Id (G)),
                     F1        => G,
                     Kind      => High_Check_Kind,
                     Tag       => "uninitialized");
                  Found_Uninitialized := True;
               end if;
            end loop;
         end loop;

         if Found_Uninitialized then
            --  If a variable or state abstraction that has not been
            --  mentioned in an Initializes aspect was found in the
            --  RHS of an initialization_item then we don't do any
            --  further analysis.
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
                       (Vars => Node_Sets.To_Set
                          (Get_Direct_Mapping_Id (G)),
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

            --  Raise warnings for actual inputs that are not
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
                          "initialization of # must not depend on #",
                        SRM_Ref   => "7.1.5(11)",
                        N         => Find_Entity
                          (Get_Direct_Mapping_Id (The_Out)),
                        F1        => The_Out,
                        F2        => Actual_In,
                        Tag       => "initializes_wrong",
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

            --  Raise warnings for inputs mentioned in the Initializes
            --  that are not actual inputs.
            for Contract_In of All_Contract_Ins loop
               if not All_Actual_Ins.Contains (Contract_In) then
                  Error_Msg_Flow
                    (FA        => FA,
                     Msg       => "initialization of # does not depend on #",
                     SRM_Ref   => "7.1.5(11)",
                     N         => Find_Entity
                       (Get_Direct_Mapping_Id (The_Out)),
                     F1        => The_Out,
                     F2        => Contract_In,
                     Tag       => "initializes_wrong",
                     Kind      => Medium_Check_Kind);
               end if;
            end loop;
         end loop;
      end;
   end Check_Initializes_Contract;

end Flow.Analysis;
