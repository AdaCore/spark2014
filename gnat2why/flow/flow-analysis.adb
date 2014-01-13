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

with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with Snames;                use Snames;

with Why;

with Gnat2Why_Args;
with SPARK_Util;            use SPARK_Util;

with Flow.Utility;          use Flow.Utility;
with Flow_Error_Messages;   use Flow_Error_Messages;
with Flow_Tree_Utility;     use Flow_Tree_Utility;

--  with Output;                use Output;
--  with Treepr;                use Treepr;
with Flow.Debug;            use Flow.Debug;

package body Flow.Analysis is

   Debug_Trace_Depends : constant Boolean := False;
   --  Enable this to show the specified and computed dependency relation.

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Node_Sets.Set;
   use type Flow_Id_Sets.Set;

   function Error_Location (G : Flow_Graphs.T'Class;
                            V : Flow_Graphs.Vertex_Id)
                            return Node_Or_Entity_Id;
   --  Find a good place to raise an error for vertex V.

   function Get_Line (G   : Flow_Graphs.T'Class;
                      V   : Flow_Graphs.Vertex_Id;
                      Sep : Character := ':')
                      return String;
   --  Obtain the location for the given vertex as in "foo.adb:12".

   procedure Write_Vertex_Set
     (G        : Flow_Graphs.T;
      Set      : Vertex_Sets.Set;
      Filename : String);
   --  Write a trace file for GPS.

   procedure Global_Required
     (FA  : Flow_Analysis_Graphs;
      Var : Flow_Id)
   with Pre  => Var.Kind = Magic_String;
   --  Emit an error message that (the first call) introducing the
   --  global Var requires a global annotation.

   function Find_Global (S : Entity_Id;
                         F : Flow_Id)
                         return Node_Id;
   --  Find the given global F in the subprogram declaration of S (or
   --  in the initializes clause of S). If we can't find it (perhaps
   --  because of computed globals) we just return S which is a useful
   --  fallback place to raise an error.

   type Var_Use_Kind is (Use_Read, Use_Write, Use_Any);

   function First_Variable_Use (N       : Node_Id;
                                FA      : Flow_Analysis_Graphs;
                                Scope   : Flow_Scope;
                                Var     : Flow_Id;
                                Precise : Boolean)
                                return Node_Id;
   --  Given a node N, we traverse the tree to find the most deeply
   --  nested node which still uses Var. If Precise is True look only
   --  for Var (for example R.Y), otherwise we also look for the
   --  entire variable represented by Var (in our example we'd also
   --  look for R).
   --
   --  If we cannot find any suitable node we return N itself.

   function First_Variable_Use (FA      : Flow_Analysis_Graphs;
                                Var     : Flow_Id;
                                Kind    : Var_Use_Kind;
                                Precise : Boolean)
                                return Node_Id;
   --  Find a suitable node in the tree which uses the given
   --  variable. If Precise is True look only for Var (for example
   --  R.Y), otherwise we also look for the entire variable
   --  represented by Var (in our example we'd also look for R).
   --
   --  If no suitable node can be found we return FA.Analyzed_Entity
   --  as a fallback.

   --------------------
   -- Error_Location --
   --------------------

   function Error_Location (G : Flow_Graphs.T'Class;
                            V : Flow_Graphs.Vertex_Id)
                            return Node_Or_Entity_Id
   is
      K : constant Flow_Id      := G.Get_Key (V);
      A : constant V_Attributes := G.Get_Attributes (V);
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

   function Get_Line (G   : Flow_Graphs.T'Class;
                      V   : Flow_Graphs.Vertex_Id;
                      Sep : Character := ':')
                      return String
   is
      N       : constant Node_Or_Entity_Id := Error_Location (G, V);
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
     (G        : Flow_Graphs.T;
      Set      : Vertex_Sets.Set;
      Filename : String)
   is
      FD       : Ada.Text_IO.File_Type;
   begin
      if not Set.Is_Empty then

         Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, Filename);

         for V of Set loop
            declare
               F : constant Flow_Id := G.Get_Key (V);
            begin
               if F.Kind = Direct_Mapping then
                  Ada.Text_IO.Put (FD, Get_Line (G, V));
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
     (FA  : Flow_Analysis_Graphs;
      Var : Flow_Id)
   is
      First_Use : Node_Id;
      Tracefile : Unbounded_String;
   begin

      First_Use := First_Variable_Use (FA      => FA,
                                       Var     => Var,
                                       Kind    => Use_Any,
                                       Precise => True);

      if First_Use = FA.Analyzed_Entity then
         --  Ok, we did not actually find a node which make use of
         --  Var, which is a bit odd. This means that the computed
         --  globals for FA.Analyzed_Entity contain a symbol Var for
         --  no good reason.
         Error_Msg_Flow
           (FA        => FA,
            Tracefile => Tracefile,
            Msg       => "bug: & contains reference to &, " &
              "but no use can be found",
            N         => FA.Analyzed_Entity,
            F1        => Direct_Mapping_Id (FA.Analyzed_Entity),
            F2        => Var);

      else
         pragma Assert (Nkind (First_Use) in N_Subprogram_Call);

         Error_Msg_Flow
           (FA        => FA,
            Tracefile => Tracefile,
            Msg       => "called subprogram & requires GLOBAL " &
              "aspect to make state visible",
            N         => First_Use,
            F1        => Direct_Mapping_Id (Entity (Name (First_Use))));
      end if;

   end Global_Required;

   -----------------
   -- Find_Global --
   -----------------

   function Find_Global (S : Entity_Id;
                         F : Flow_Id)
                         return Node_Id
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
   -- First_Variable_Use --
   ------------------------

   function First_Variable_Use (N       : Node_Id;
                                FA      : Flow_Analysis_Graphs;
                                Scope   : Flow_Scope;
                                Var     : Flow_Id;
                                Precise : Boolean)
                                return Node_Id
   is
      First_Use : Node_Id := N;
      Var_Tgt   : constant Flow_Id :=
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
                              Scope            => Scope,
                              Local_Constants  => FA.Local_Constants,
                              Reduced          => not Precise,
                              Allow_Statements => True).Contains (Var_Tgt)
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
      Search_Expression (N);
      return First_Use;
   end First_Variable_Use;

   function First_Variable_Use (FA      : Flow_Analysis_Graphs;
                                Var     : Flow_Id;
                                Kind    : Var_Use_Kind;
                                Precise : Boolean)
                                return Node_Id
   is
      Var_Normal   : constant Flow_Id := Change_Variant (Var, Normal_Use);
      E_Var_Normal : constant Flow_Id := Entire_Variable (Var_Normal);

      First_Use : Node_Id := FA.Analyzed_Entity;

      procedure Proc (V      : Flow_Graphs.Vertex_Id;
                      Origin : Flow_Graphs.Vertex_Id;
                      Depth  : Natural;
                      T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Checks if vertex V contains a reference to Var. If so, we
      --  set First_Use and abort the search.

      ----------
      -- Proc --
      ----------

      procedure Proc (V      : Flow_Graphs.Vertex_Id;
                      Origin : Flow_Graphs.Vertex_Id;
                      Depth  : Natural;
                      T_Ins  : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         pragma Unreferenced (Origin, Depth);

         Atr         : constant V_Attributes := FA.CFG.Get_Attributes (V);
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

         if (Atr.Is_Program_Node or Atr.Is_Precondition) and
           not Atr.Is_Callsite
         then
            First_Use := Get_Direct_Mapping_Id (FA.CFG.Get_Key (V));
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
      Tracefile   : Unbounded_String;
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
               Tracefile => Tracefile,
               Msg       => "& might not be initialized after elaboration " &
                 "of main program &",
               N         => Find_Global (FA.Analyzed_Entity, R),
               F1        => R,
               F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
               Tag       => "uninitialized",
               Warning   => True);
         end if;

      end loop;
   end Analyse_Main;

   ------------------
   -- Sanity_Check --
   ------------------

   procedure Sanity_Check
     (FA   : Flow_Analysis_Graphs;
      Sane : out Boolean)
   is
      Tracefile  : Unbounded_String;
      Entry_Node : Node_Id;

      function Check_Expressions_Variable_Free
        (N : Node_Id) return Traverse_Result;
      --  Check that expressions used in certain contexts are free of
      --  variables, as per SPARK RM 4.4(2). This function deals with
      --  the following contexts:
      --     Component Declarations
      --     Discriminant Specifications
      --     Object Renaming Declarations

      -------------------------------------
      -- Check_Expressions_Variable_Free --
      -------------------------------------

      function Check_Expressions_Variable_Free
        (N : Node_Id) return Traverse_Result
      is
         ES1 : constant String := "default initialization ";
         ES2 : constant String := "subtype constraint ";
         ES3 : constant String := "cannot depend on &";
         ES4 : constant String := "renamed index ";
         ES5 : constant String := "renamed slice ";

         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Msg  : String;
            Err_Node : Node_Id);
         --  Iterates over Flow_Ids. An error is issued for any member of that
         --  set which does NOT denote a constant.

         function Check_Name (N : Node_Id) return Traverse_Result;
         --  Checks indexed components and slices which are part
         --  of a Name subtree.

         -----------------------
         -- Check_Flow_Id_Set --
         -----------------------

         procedure Check_Flow_Id_Set
           (Flow_Ids : Ordered_Flow_Id_Sets.Set;
            Err_Msg  : String;
            Err_Node : Node_Id) is
         begin
            for F of Flow_Ids loop
               if F.Kind = Direct_Mapping
                 and then not Is_Constant_Object (F.Node)
               then
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => Err_Msg,
                     SRM_Ref   => "4.4(2)",
                     N         => Err_Node,
                     F1        => F);
                  Sane := False;
               end if;
            end loop;
         end Check_Flow_Id_Set;

         ----------------
         -- Check_Name --
         ----------------

         function Check_Name (N : Node_Id) return Traverse_Result is
         begin
            case Nkind (N) is

               when N_Indexed_Component =>
                  declare
                     Renamed_Indexes : constant List_Id :=
                       Expressions (N);
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       To_Ordered_Flow_Id_Set
                       (Get_Variable_Set
                          (L                            =>
                             Renamed_Indexes,
                           Scope                        =>
                             Get_Flow_Scope (N),
                           Local_Constants              =>
                             Node_Sets.Empty_Set,
                           Expand_Synthesized_Constants =>
                             True));
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Msg  => ES4 & ES3,
                                        Err_Node => N);
                  end;
               when N_Slice =>
                  declare
                     Renamed_Slice : constant Node_Id :=
                       Discrete_Range (N);
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       To_Ordered_Flow_Id_Set
                       (Get_Variable_Set
                          (N                            =>
                             Renamed_Slice,
                           Scope                        =>
                             Get_Flow_Scope (Renamed_Slice),
                           Local_Constants              =>
                             Node_Sets.Empty_Set,
                           Expand_Synthesized_Constants =>
                             True));
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Msg  => ES5 & ES3,
                                        Err_Node => Renamed_Slice);
                  end;

               when others =>
                  null;
            end case;
            return OK; -- Keep searching in case of nested prefixes
         end Check_Name;

         procedure Check_Name_Indexes_And_Slices is new
           Traverse_Proc (Check_Name);

      --  Start of Check_Expressions_Variable_Free

      begin
         case Nkind (N) is
            when N_Subprogram_Body |
                 N_Package_Specification |
                 N_Package_Body =>
               --  We do not want to process declarations of any nested
               --  subprograms or packages. These will be analyzed by their
               --  own pass of flow analysis.
               if N = Entry_Node then
                  return OK;
               else
                  return Skip;
               end if;

            when N_Loop_Parameter_Specification =>
               --  In a loop parameter specification, variables are allowed
               --  in the range constraint, so the tree walk is pruned here.
               return Skip;

            when N_Object_Renaming_Declaration =>

               Check_Name_Indexes_And_Slices (Name (N));
               return Skip;

            when N_Subtype_Indication =>

               Subtype_Indication : declare
                  C : constant Node_Id := Constraint (N);
               begin
                  case Nkind (C) is
                     when N_Range_Constraint =>
                        declare
                           --  Note that fetching the variable set for C
                           --  returns the union of the sets of the low-bound
                           --  and the high-bound.
                           Deps : constant Ordered_Flow_Id_Sets.Set :=
                             To_Ordered_Flow_Id_Set
                               (Get_Variable_Set
                                  (N                            => C,
                                   Scope                        =>
                                     Get_Flow_Scope (C),
                                   Local_Constants              =>
                                     Node_Sets.Empty_Set,
                                   Expand_Synthesized_Constants =>
                                     True));
                        begin
                           Check_Flow_Id_Set (Flow_Ids => Deps,
                                              Err_Msg  => ES2 & ES3,
                                              Err_Node => C);
                        end;

                        return Skip;

                     when N_Index_Or_Discriminant_Constraint =>
                        declare
                           Deps : constant Ordered_Flow_Id_Sets.Set :=
                             To_Ordered_Flow_Id_Set
                               (Get_Variable_Set
                                  (L                            =>
                                     Constraints (C),
                                   Scope                        =>
                                     Get_Flow_Scope (C),
                                   Local_Constants              =>
                                     Node_Sets.Empty_Set,
                                   Expand_Synthesized_Constants =>
                                     True));
                        begin
                           Check_Flow_Id_Set (Flow_Ids => Deps,
                                              Err_Msg  => ES2 & ES3,
                                              Err_Node => C);
                        end;

                        return Skip;

                     when N_Digits_Constraint |
                          N_Delta_Constraint =>
                        --  Ada LRM requires these constraints to be static,
                        --  so no further action required here.
                        return Skip;

                     when others =>
                        return OK;
                  end case;
               end Subtype_Indication;

            when N_Component_Declaration |
                 N_Discriminant_Specification =>

               if Present (Expression (N)) then
                  declare
                     Deps : constant Ordered_Flow_Id_Sets.Set :=
                       To_Ordered_Flow_Id_Set
                       (Get_Variable_Set
                          (N                            =>
                             Expression (N),
                           Scope                        =>
                             Get_Flow_Scope (N),
                           Local_Constants              =>
                             Node_Sets.Empty_Set,
                           Expand_Synthesized_Constants =>
                             True));
                  begin
                     Check_Flow_Id_Set (Flow_Ids => Deps,
                                        Err_Msg  => ES1 & ES3,
                                        Err_Node => Expression (N));
                  end;
               end if;

               return Skip;
            when others =>
               return OK;
         end case;
      end Check_Expressions_Variable_Free;

      procedure Check_Expressions is
        new Traverse_Proc (Check_Expressions_Variable_Free);

   --  Start of Sanity_Check

   begin
      --  Innocent until proven guilty.
      Sane := True;

      --  Sanity check for functions with global outputs.
      if Ekind (FA.Analyzed_Entity) = E_Function
        and then FA.Function_Side_Effects_Present
      then
         if Gnat2Why_Args.Flow_Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Tracefile => Tracefile,
               Msg       => "flow analysis of & abandoned due to " &
                 "function with side effects",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
         Sane := False;
         return;
      end if;

      --  Sanity check for aliasing.

      pragma Assert_And_Cut (Sane);

      if FA.Aliasing_Present then
         if Gnat2Why_Args.Flow_Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Tracefile => Tracefile,
               Msg       => "flow analysis of & abandoned due to aliasing",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
         Sane := False;
         return;
      end if;

      --  Sanity check for bad default initializations.

      pragma Assert_And_Cut (Sane);

      --  Please don't try to simplify/delete Entry_Node here, it is also a
      --  global in Check_Expressions.

      case FA.Kind is
         when E_Subprogram_Body =>
            Entry_Node := SPARK_Util.Get_Subprogram_Body (FA.Analyzed_Entity);
            pragma Assert (Nkind (Entry_Node) = N_Subprogram_Body);
            Check_Expressions (Entry_Node);

         when E_Package =>
            Entry_Node := Get_Enclosing (FA.Analyzed_Entity,
                                         N_Package_Specification);
            Check_Expressions (Entry_Node);

         when E_Package_Body =>
            Entry_Node := Get_Enclosing (FA.Spec_Node,
                                         N_Package_Specification);
            Check_Expressions (Entry_Node);

            Entry_Node := Get_Enclosing (FA.Analyzed_Entity,
                                         N_Package_Body);
            Check_Expressions (Entry_Node);
      end case;

      if not Sane then
         if Gnat2Why_Args.Flow_Debug_Mode then
            Error_Msg_Flow
              (FA        => FA,
               Tracefile => Tracefile,
               Msg       => "flow analysis of & abandoned due to " &
                 "expressions with variable inputs",
               N         => FA.Analyzed_Entity,
               F1        => Direct_Mapping_Id (FA.Analyzed_Entity));
         end if;
         return;
      end if;

      --  Sanity check all read vertices to see if the read is legal.

      pragma Assert_And_Cut (Sane);

      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         if FA.PDG.Get_Key (V).Variant /= Final_Value then
            for R of FA.PDG.Get_Attributes (V).Variables_Explicitly_Used loop
               case R.Kind is
                  when Direct_Mapping | Record_Field =>
                     if Ekind (Get_Direct_Mapping_Id (R)) =
                       E_Out_Parameter and then
                       Is_Volatile (R)
                     then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "volatile formal out & cannot be read",
                           SRM_Ref   => "7.1.3(14)",
                           N   => Error_Location (FA.PDG, V),
                           F1  => Entire_Variable (R));
                        Sane := False;
                     end if;

                  when Magic_String =>
                     --  Nothing to do in this case.
                     null;

                  when Null_Value | Synthetic_Null_Export =>
                     raise Why.Unexpected_Node;
               end case;
            end loop;
         end if;
      end loop;
      if not Sane then
         return;
      end if;

      --  Sanity check all written vertices to see if the write is
      --  legal.

      pragma Assert_And_Cut (Sane);

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.PDG.Get_Attributes (V);

            Written_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Defined);

            F                    : Flow_Id;
            Corresp_Final_Vertex : Flow_Graphs.Vertex_Id;
            Final_Atr            : V_Attributes;
         begin
            for Var of Written_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if not (FA.All_Vars.Contains (F) or Synthetic (F)) and
                 FA.Kind in E_Package | E_Package_Body
               then

                  --  We have a write to a variable a package knows
                  --  nothing about. This is always an illegal update.

                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "cannot write & during " &
                             "elaboration of &",
                           SRM_Ref   => "7.7.1(5)",
                           N   => Error_Location (FA.PDG, V),
                           F1  => Entire_Variable (Var),
                           F2  => Direct_Mapping_Id (FA.Analyzed_Entity));

                     when Magic_String =>
                        Global_Required (FA, Var);

                     when others =>
                        raise Program_Error;
                  end case;
                  Sane := False;

               elsif not FA.All_Vars.Contains (F) then

                  --  This case is dealt with in the next sanity
                  --  check.

                  null;

               elsif FA.PDG.Get_Key (V).Variant not in
                 Initial_Value | Final_Value
               then

                  --  We do know about that particular global. Now we
                  --  need to check if the update is OK.

                  Corresp_Final_Vertex :=
                    FA.PDG.Get_Vertex (Change_Variant (Var, Final_Value));
                  pragma Assert (Corresp_Final_Vertex /=
                                   Flow_Graphs.Null_Vertex);
                  Final_Atr := FA.PDG.Get_Attributes (Corresp_Final_Vertex);

                  if Final_Atr.Is_Global and
                    Final_Atr.Is_Constant and
                    not Final_Atr.Is_Loop_Parameter
                  then

                     if FA.Kind in E_Package | E_Package_Body then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "cannot write & during " &
                             "elaboration of &",
                           SRM_Ref   => "7.7.1(5)",
                           N         => Error_Location (FA.PDG, V),
                           F1        => Var,
                           F2        => Direct_Mapping_Id
                             (FA.Analyzed_Entity));

                     else
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "& must be a global output of &",
                           SRM_Ref   => "6.1.4",
                           N         => Error_Location (FA.PDG, V),
                           F1        =>
                             (if A.Is_Parameter
                              then A.Parameter_Formal
                              else Var),
                           F2        => Direct_Mapping_Id (FA.Analyzed_Entity),
                           Tag       => "illegal_update");
                     end if;
                     Sane := False;

                  end if;

               end if;

            end loop;
         end;
      end loop;
      if not Sane then
         return;
      end if;

      --  Sanity check all vertices if they mention a flow id that we
      --  do not know about.

      pragma Assert_And_Cut (Sane);

      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.CFG.Get_Attributes (V);

            All_Vars : constant Ordered_Flow_Id_Sets.Set :=
              To_Ordered_Flow_Id_Set (A.Variables_Used or A.Variables_Defined);

            Aspect_To_Fix : constant String :=
              (case FA.Kind is
                  when E_Subprogram_Body => (if Present (FA.Refined_Global_N)
                                             then "Refined_Global"
                                             else "Global"),
                  when others            => "Initializes");

            SRM_Ref : constant String :=
              (case FA.Kind is
                  when E_Subprogram_Body => "6.1.4(13)",
                  when others            => "7.1.5(12)");

            F : Flow_Id;
         begin
            for Var of All_Vars loop
               F := Change_Variant (Var, Normal_Use);

               if not (FA.All_Vars.Contains (F) or Synthetic (F)) then

                  --  Here we are dealing with a missing global.
                  case F.Kind is
                     when Direct_Mapping | Record_Field =>
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "& must be listed in the " &
                             Aspect_To_Fix & " aspect of &",
                           SRM_Ref   => SRM_Ref,
                           N   => First_Variable_Use (FA      => FA,
                                                      Var     => Var,
                                                      Kind    => Use_Read,
                                                      Precise => False),
                           F1  => Entire_Variable (Var),
                           F2  => Direct_Mapping_Id (FA.Analyzed_Entity));

                     when Magic_String =>
                        Global_Required (FA, Var);

                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
                  Sane := False;
               end if;

            end loop;
         end;
      end loop;
   end Sanity_Check;

   --------------------------------
   -- Sanity_Check_Postcondition --
   --------------------------------

   procedure Sanity_Check_Postcondition (FA   : Flow_Analysis_Graphs;
                                         Sane : in out Boolean)
   is
      Vars_Used  : Flow_Id_Sets.Set;
      Vars_Known : Flow_Id_Sets.Set;
      Tracefile  : Unbounded_String;
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
                           Scope           => Get_Flow_Scope (Expr),
                           Local_Constants => FA.Local_Constants,
                           Reduced         => True));
                  when others =>
                     Vars_Used := To_Entire_Variables
                       (Get_Variable_Set
                          (Expr,
                           Scope           => Private_Scope (Get_Flow_Scope
                                                               (Expr)),
                           Local_Constants => FA.Local_Constants,
                           Reduced         => True));
               end case;
               Vars_Used.Difference (Quantified_Variables (Expr));

               for Var of Vars_Used loop
                  if not Vars_Known.Contains (Var) then
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
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
                        F2        => Direct_Mapping_Id (FA.Analyzed_Entity));
                     Sane := False;

                  elsif FA.Kind in E_Package | E_Package_Body
                    and then Is_Library_Level_Entity (FA.Analyzed_Entity)
                    and then not Is_Initialized_At_Elaboration (Var,
                                                                FA.B_Scope)
                  then

                     --  If check an initial_condition aspect, we make sure
                     --  that all variables mentioned are also mentioned in
                     --  an initializes aspect.

                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "& must be initialized at elaboration",
                        N         => First_Variable_Use (N       => Expr,
                                                         FA      => FA,
                                                         Scope   => FA.B_Scope,
                                                         Var     => Var,
                                                         Precise => False),
                        F1        => Entire_Variable (Var));
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
      Tracefile : Unbounded_String;

      Written_Entire_Vars : Flow_Id_Sets.Set;
      Unwritten_Vars      : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         F_Final := FA.PDG.Get_Key (V);
         A_Final := FA.PDG.Get_Attributes (V);
         if F_Final.Variant = Final_Value and then
           A_Final.Is_Export
         then

            --  We have a final use vertex which is an export that has
            --  a single in-link. If this in-link is its initial value
            --  then clearly we do not set defined this output on any
            --  path.

            Unwritten := False;
            if FA.PDG.In_Neighbour_Count (V) = 1 then
               F_Initial := FA.PDG.Get_Key (FA.PDG.Parent (V));
               A_Initial := FA.PDG.Get_Attributes (FA.PDG.Parent (V));
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
         A_Final := FA.PDG.Get_Attributes (V);

         if not Written_Entire_Vars.Contains (Entire_Variable (F_Final)) then

            if not (F_Final.Kind in Direct_Mapping | Record_Field)
              or else not FA.Unmodified_Vars.Contains
                            (Get_Direct_Mapping_Id (F_Final))
            then

               if A_Final.Is_Global then
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => "& is not modified, could be INPUT",
                     N         => Find_Global (FA.Analyzed_Entity, F_Final),
                     F1        => F_Final,
                     Tag       => "inout_only_read",
                     Warning   => True);
               else
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => "& is not modified, could be IN",
                     N         => Error_Location (FA.PDG, V),
                     F1        => F_Final,
                     Tag       => "inout_only_read",
                     Warning   => True);
               end if;
            end if;
         end if;
      end loop;
   end Find_Unwritten_Exports;

   ------------------------------
   -- Find_Ineffective_Imports --
   ------------------------------

   procedure Find_Ineffective_Imports (FA : in out Flow_Analysis_Graphs) is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean
      is (FA.PDG.Get_Key (V).Variant = Final_Value and then
            FA.PDG.Get_Attributes (V).Is_Export);
      --  Checks if the given vertex V is a final-use vertex.

      Effective_Ids : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Entire_Ids    : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Tracefile     : Unbounded_String;
   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr : constant V_Attributes := FA.PDG.Get_Attributes (V);
         begin
            if Key.Variant = Initial_Value
              and then Atr.Is_Initialized
              and then (not Atr.Is_Loop_Parameter)
            then
               --  Note the entire variable.
               declare
                  P : Flow_Graphs.Vertex_Id := V;
               begin
                  while P /= Flow_Graphs.Null_Vertex loop
                     if FA.CFG.Parent (P) = Flow_Graphs.Null_Vertex then
                        Entire_Ids.Include (P);
                        exit;
                     end if;
                     P := FA.CFG.Parent (P);
                  end loop;
               end;

               --  Check if we're ineffective or not.
               if FA.PDG.Non_Trivial_Path_Exists (V,
                                                  Is_Final_Use'Access)
               then
                  --  We can reach a final use vertex, so we are doing
                  --  something useful. We flag up the entire chain as
                  --  being useful.
                  Effective_Ids.Include (V);
                  declare
                     P : Flow_Graphs.Vertex_Id := V;
                  begin
                     while P /= Flow_Graphs.Null_Vertex loop
                        Effective_Ids.Include (P);
                        P := FA.CFG.Parent (P);
                     end loop;
                  end;
               else
                  --  We cannot reach any final use vertex, hence the
                  --  import of V is ineffective.
                  null;
               end if;
            end if;
         end;
      end loop;

      --  Now that we can issue error messages. We can't do it inline
      --  because we need to pay special attention to records.
      for V of Entire_Ids loop
         declare
            F : constant Flow_Id      := FA.PDG.Get_Key (V);
            A : constant V_Attributes := FA.PDG.Get_Attributes (V);
         begin
            if not Effective_Ids.Contains (V) then

               if not (F.Kind in Direct_Mapping | Record_Field)
                 or else not FA.Unreferenced_Vars.Contains
                               (Get_Direct_Mapping_Id (F))
               then

                  if Is_Discriminant (F) then
                     --  Discriminants are never ineffective imports.
                     null;
                  elsif A.Mode = Mode_Proof then
                     --  Proof_Ins are never ineffective imports.
                     null;
                  elsif A.Is_Global then
                     if FA.Kind = E_Subprogram_Body and then
                       not FA.Is_Generative
                     then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       =>
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
                           N         => Find_Global (FA.Analyzed_Entity, F),
                           F1        => F,
                           Tag       => "unused_initial_value",
                        Warning => True);
                     end if;
                  else
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "unused initial value of &",
                        --  ??? find_import
                        N         => Error_Location (FA.PDG, V),
                        F1        => F,
                        Tag       => "unused_initial_value",
                        Warning   => True);
                  end if;
               end if;
            end if;
         end;
      end loop;
   end Find_Ineffective_Imports;

   ---------------------------------
   -- Find_Ineffective_Statements --
   ---------------------------------

   procedure Find_Ineffective_Statements (FA : in out Flow_Analysis_Graphs) is
      Tracefile : Unbounded_String;

      function Is_Final_Use_Any_Export (V : Flow_Graphs.Vertex_Id)
                                        return Boolean;
      --  Checks if the given vertex V is a final-use vertex that is
      --  also an export.

      function Is_Any_Final_Use (V : Flow_Graphs.Vertex_Id)
                                 return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Is_Dead_End (V : Flow_Graphs.Vertex_Id)
                            return Boolean;
      --  Checks if from the given vertex V it is impossible to reach the
      --  end vertex.

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
           FA.PDG.Get_Attributes (V).Is_Export;
      end Is_Final_Use_Any_Export;

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
           FA.CFG.Get_Attributes (Ineffective_Statement).Variables_Defined;

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
              (FA.CFG.Get_Attributes (V).Variables_Defined -
                 FA.CFG.Get_Attributes (V).Variables_Used);
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
            Atr : constant V_Attributes := FA.CFG.Get_Attributes (V);
         begin
            if Atr.No_Return_From_Here then
               TV := Flow_Graphs.Skip_Children;
            elsif V = FA.End_Vertex then
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

   begin --  Find_Ineffective_Statements
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            N    : Node_Id;
            Key  : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr  : constant V_Attributes := FA.PDG.Get_Attributes (V);
            Mask : Vertex_Sets.Set;
            Tag  : constant String := "ineffective";
            Tmp  : Flow_Id;
         begin
            if Atr.Is_Program_Node or
              Atr.Is_Parameter or
              Atr.Is_Global_Parameter
            then
               --  A vertex is ineffective if there is no path in the
               --  PDG to *any* final use vertex that is also an
               --  export.
               --
               --  If we analyse a package, we supress this message if
               --  we don't have a initializes clause *and* the the
               --  given vertex has an effect on any final use (export
               --  or otherwise).
               if
                 --  Basic check here
                 not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use_Any_Export'Access) and then

                 --  Supression for dead code
                 not Is_Dead_End (V) and then

                 --  Supression for packages without initializes
                 (if FA.Kind in E_Package | E_Package_Body and then
                    not Present (FA.Initializes_N)
                  then
                     not FA.PDG.Non_Trivial_Path_Exists
                       (V, Is_Any_Final_Use'Access))
               then
                  Mask := Find_Masking_Code (V);
                  if FA.PDG.Get_Key (V) = Null_Flow_Id then
                     N := Empty;
                  else
                     N := Get_Direct_Mapping_Id (FA.PDG.Get_Key (V));
                  end if;

                  if Atr.Is_Parameter or Atr.Is_Global_Parameter then
                     if Atr.Is_Parameter then
                        Tmp := Direct_Mapping_Id
                          (Skip_Any_Conversions
                             (Get_Direct_Mapping_Id (Atr.Parameter_Actual)));
                     else
                        Tmp := Atr.Parameter_Formal;
                     end if;

                     if Key.Variant = In_View then
                        --  For in parameters we do not emit the
                        --  ineffective assignment error as its a bit
                        --  confusing.
                        null;

                     elsif Atr.Is_Discriminants_Only_Parameter then
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
                           N         => Error_Location (FA.PDG, V),
                           F1        => Tmp,
                           Tag       => Tag,
                           Warning   => True);

                     else
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "unused assignment",
                           N         => Error_Location (FA.PDG, V),
                           Tag       => Tag,
                           Warning   => True);
                     end if;

                  elsif Nkind (N) = N_Assignment_Statement then
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "unused assignment",
                        N         => Error_Location (FA.PDG, V),
                        Tag       => Tag,
                        Warning   => True);

                  elsif Nkind (N) = N_Object_Declaration then
                     if not Constant_Present (N) then
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "initialization has no effect",
                           N         => Error_Location (FA.PDG, V),
                           Tag       => Tag,
                           Warning   => True);
                     end if;
                     --  This warning is ignored for local constants.

                  else
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "statement has no effect",
                        N         => Error_Location (FA.PDG, V),
                        Tag       => Tag,
                        Warning   => True);

                  end if;
                  if Mask.Length >= 1 then
                     Write_Vertex_Set
                       (G        => FA.PDG,
                        Set      => Mask,
                        Filename => To_String (Tracefile));
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
         Atr : constant V_Attributes := FA.CFG.Get_Attributes (V);
      begin
         Dead_Code.Exclude (V);

         if Atr.No_Return_From_Here then
            TV := Flow_Graphs.Skip_Children;
         else
            TV := Flow_Graphs.Continue;
         end if;
      end Flag_Live;

   begin
      --  Guilty until proven innocent.
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Atr : constant V_Attributes := FA.CFG.Get_Attributes (V);
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
            Unused : Unbounded_String;
         begin
            Error_Msg_Flow (FA        => FA,
                            Tracefile => Unused,
                            Msg       => "dead code",
                            N         => Get_Direct_Mapping_Id
                              (FA.CFG.Get_Key (V)),
                            Tag       => "dead_code",
                            Warning   => False);
         end;
      end loop;
   end Find_Dead_Code;

   -----------------------
   -- Enforce_No_Return --
   -----------------------

   procedure Enforce_No_Return (FA : in out Flow_Analysis_Graphs)
   is
      procedure Search (V   : Flow_Graphs.Vertex_Id;
                        Ins : out Flow_Graphs.Traversal_Instruction);
      --  Traverse graph (but don't cross no_return nodes). Stop at end.

      procedure Step (V : Flow_Graphs.Vertex_Id);
      --  Record the path.

      procedure Search (V   : Flow_Graphs.Vertex_Id;
                        Ins : out Flow_Graphs.Traversal_Instruction)
      is
         Atr : constant V_Attributes := FA.CFG.Get_Attributes (V);
      begin
         if V = FA.End_Vertex then
            Ins := Flow_Graphs.Found_Destination;
         elsif Atr.No_Return_From_Here then
            Ins := Flow_Graphs.Skip_Children;
         else
            Ins := Flow_Graphs.Continue;
         end if;
      end Search;

      The_Path : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Step (V : Flow_Graphs.Vertex_Id)
      is
      begin
         The_Path.Include (V);
      end Step;

      Tracefile : Unbounded_String;

   begin
      if FA.Kind /= E_Subprogram_Body or else
        not No_Return (FA.Analyzed_Entity)
      then
         --  Nothing to do in this case.
         return;
      end if;

      pragma Assert_And_Cut (No_Return (FA.Analyzed_Entity));

      --  If we can find a path from start -> end, then clearly we can
      --  return...

      FA.CFG.Shortest_Path (Start => FA.Start_Vertex,
                            Allow_Trivial => True,
                            Search        => Search'Access,
                            Step          => Step'Access);

      if The_Path.Length >= 1 then
         Error_Msg_Flow (FA        => FA,
                         Tracefile => Tracefile,
                         Msg       => "no_return subprogram & must not return",
                         SRM_Ref   => "6.5.1",
                         N         => FA.Analyzed_Entity,
                         F1        => Direct_Mapping_Id (FA.Analyzed_Entity),
                         Tag       => "no_return");
         Write_Vertex_Set (G        => FA.CFG,
                           Set      => The_Path,
                           Filename => To_String (Tracefile));
      end if;
   end Enforce_No_Return;

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
      --  Sets Found to wheather the variable corresponding to V_Initial is
      --  defined on any of the paths that lead to V_Use. V_Error is the
      --  vertex where the message should be emmited.

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
            A : constant V_Attributes := FA.CFG.Get_Attributes (V);
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

         Write_Vertex_Set (G        => FA.CFG,
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
                 and then FA.CFG.Get_Attributes
                            (V).Variables_Defined.Contains (The_Var)
               then
                  TV := Flow_Graphs.Skip_Children;
               elsif V /= Flow_Graphs.Null_Vertex
                 and then FA.CFG.Get_Key (V).Variant /= Final_Value
                 and then FA.CFG.Get_Attributes
                            (V).Variables_Explicitly_Used.Contains (The_Var)
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
               if FA.CFG.Get_Attributes (V).Variables_Defined.Contains
                 (The_Var)
               then

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
                    and then not FA.PDG.Get_Attributes
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
            Atr_I : constant V_Attributes := FA.PDG.Get_Attributes (V_Initial);
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
                     Atr_U : constant V_Attributes :=
                       FA.PDG.Get_Attributes (V_Use);

                     Action : constant String := (if Has_Async_Readers (Key_I)
                                                  then "written"
                                                  else "initialized");

                     Defined_Elsewhere : Boolean;
                     V_Error           : Flow_Graphs.Vertex_Id;
                  begin

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

                        if Atr_U.Is_Global then
                           if Defined_Elsewhere then
                              Error_Msg_Flow
                                (FA        => FA,
                                 Tracefile => Tracefile,
                                 Msg       => "& might not be " & Action,
                                 N         => Find_Global
                                   (FA.Analyzed_Entity, Key_I),
                                 F1        => Key_I,
                                 Tag       => "uninitialized",
                                 Warning   => True);
                           else
                              Error_Msg_Flow
                                (FA        => FA,
                                 Tracefile => Tracefile,
                                 Msg       => "& is not " & Action,
                                 N         => Find_Global
                                   (FA.Analyzed_Entity, Key_I),
                                 F1        => Key_I,
                                 Tag       => "uninitialized");
                           end if;
                           Mark_Definition_Free_Path
                             (From => FA.Start_Vertex,
                              To   => FA.End_Vertex,
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
                                 Tracefile => Tracefile,
                                 Msg       =>
                                   "possibly missing return statement in &",
                                 N         =>
                                   Error_Location (FA.PDG, FA.Start_Vertex),
                                 F1        => Direct_Mapping_Id
                                   (FA.Analyzed_Entity),
                                 Tag       => "missing_return");
                              Mark_Definition_Free_Path
                                (From => FA.Start_Vertex,
                                 To   => FA.End_Vertex,
                                 Var  => Change_Variant (Key_I, Normal_Use));
                           end if;

                        elsif Atr_U.Is_Export then

                           --  As we don't have a global, but an
                           --  export, it means we must be dealing
                           --  with a parameter.

                           if Defined_Elsewhere then
                              Error_Msg_Flow
                                (FA        => FA,
                                 Tracefile => Tracefile,
                                 Msg       => "& might not be " & Action &
                                   " in &",
                                 N         => Error_Location (FA.PDG, V_Error),
                                 F1        => Key_I,
                                 F2        => Direct_Mapping_Id
                                   (FA.Analyzed_Entity),
                                 Tag       => "uninitialized",
                                 Warning   => True);
                           else
                              Error_Msg_Flow
                                (FA        => FA,
                                 Tracefile => Tracefile,
                                 Msg       => "& is not " & Action & " in &",
                                 N         => Error_Location (FA.PDG, V_Error),
                                 F1        => Key_I,
                                 F2        => Direct_Mapping_Id
                                   (FA.Analyzed_Entity),
                                 Tag       => "uninitialized");
                           end if;
                           Mark_Definition_Free_Path
                             (From      => FA.Start_Vertex,
                              To        => V_Error,
                              Var       => Change_Variant (Key_I, Normal_Use),
                              V_Allowed => V_Use);

                        else

                           --  We are dealing with a local variable,
                           --  so we don't care if there is a path
                           --  where it is not set.

                           null;
                        end if;
                     else

                        --  V_Use is not a final vertex.

                        if Defined_Elsewhere then
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "& might not be " & Action,
                              N         => Error_Location (FA.PDG, V_Error),
                              F1        => Key_I,
                              Tag       => "uninitialized",
                              Warning   => True);
                        else
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "& is not " & Action,
                              N         => Error_Location (FA.PDG, V_Error),
                              F1        => Key_I,
                              Tag       => "uninitialized");
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
      Done      : Boolean       := False;
      Tmp       : Flow_Graphs.T := FA.DDG.Create;
      Is_Stable : Boolean;
      Tracefile : Unbounded_String;
   begin
      for Loop_Id of FA.Loops loop
         Done := False;
         while not Done loop
            Done := True;
            for N_Loop of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
               declare
                  Atr : V_Attributes := Tmp.Get_Attributes (N_Loop);
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
                          (N_Loop, Flow_Graphs.In_Neighbours) loop
                           if Tmp.Get_Attributes (V).Loops.Contains
                             (Loop_Id)
                           then
                              Is_Stable := False;
                              exit;
                           end if;
                        end loop;
                     end if;

                     if Is_Stable then
                        --  Remove from the loop
                        Atr.Loops.Delete (Loop_Id);
                        Tmp.Set_Attributes (N_Loop, Atr);

                        --  Complain
                        Error_Msg_Flow
                          (FA        => FA,
                           Tracefile => Tracefile,
                           Msg       => "stable",
                           N         => Error_Location (FA.PDG, N_Loop),
                           Tag       => "stable",
                           Warning   => True);

                        --  There might be other stable elements now.
                        Done := False;
                     end if;
                  end if;
               end;
            end loop;
         end loop;
      end loop;
   end Find_Stable_Elements;

   -------------------------
   -- Find_Unused_Objects --
   -------------------------

   procedure Find_Unused_Objects (FA : in out Flow_Analysis_Graphs) is
      Used_Ids   : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Entire_Ids : Vertex_Sets.Set := Vertex_Sets.Empty_Set;
      Tracefile  : Unbounded_String;
   begin
      --  First we collect a set of all unused inputs.
      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            I_F       : constant Flow_Id := FA.PDG.Get_Key (V_Initial);
            V_Final   : Flow_Graphs.Vertex_Id;
            F_F       : Flow_Id;
            Is_Unused : Boolean := False;
         begin
            if I_F.Variant = Initial_Value then
               --  For all 'initial vertices which have precisely one
               --  link...
               if FA.PDG.Out_Neighbour_Count (V_Initial) = 1 then
                  for V of FA.PDG.Get_Collection
                    (V_Initial, Flow_Graphs.Out_Neighbours)
                  loop
                     V_Final := V;
                  end loop;
                  F_F := FA.PDG.Get_Key (V_Final);
                  --  If that one link goes directly to the final use
                  --  vertex and its the only link...
                  if F_F.Variant = Final_Value and then
                    FA.PDG.In_Neighbour_Count (V_Final) = 1
                  then
                     --  then we are dealing with an unused object.
                     Is_Unused := True;
                  end if;
               end if;

               --  Note the entire variable.
               declare
                  P : Flow_Graphs.Vertex_Id := V_Initial;
               begin
                  while P /= Flow_Graphs.Null_Vertex loop
                     if FA.CFG.Parent (P) = Flow_Graphs.Null_Vertex then
                        Entire_Ids.Include (P);
                        exit;
                     end if;
                     P := FA.CFG.Parent (P);
                  end loop;
               end;

               --  Flag up records used.
               if not Is_Unused then
                  declare
                     P : Flow_Graphs.Vertex_Id := V_Initial;
                  begin
                     while P /= Flow_Graphs.Null_Vertex loop
                        Used_Ids.Include (P);
                        P := FA.CFG.Parent (P);
                     end loop;
                  end;
               end if;
            end if;
         end;
      end loop;

      --  Now that we have this set we can issue error messages. We
      --  can't do it inline because we need to pay special attention
      --  to records.
      for V of Entire_Ids loop
         if not Used_Ids.Contains (V) then
            declare
               F : constant Flow_Id      := FA.PDG.Get_Key (V);
               A : constant V_Attributes := FA.PDG.Get_Attributes (V);
            begin
               if Is_Discriminant (F) then
                  --  Discriminants can never not be used.
                  null;
               elsif A.Is_Global then
                  --  We have an unused global, we need to give the
                  --  error on the subprogram, instead of the
                  --  global. In generative mode we don't produce this
                  --  warning.

                  if not FA.Is_Generative then
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "unused global &",
                        N         => Find_Global (FA.Analyzed_Entity, F),
                        F1        => F,
                        Tag       => "unused",
                        Warning   => True);
                  end if;
               else
                  --  ??? distinguish between variables and parameters
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => "unused variable &",
                     N         => Error_Location (FA.PDG, V),
                     F1        => F,
                     Tag       => "unused",
                     Warning   => True);
               end if;
            end;
         end if;
      end loop;
   end Find_Unused_Objects;

   -------------------------------------------
   --  Find_Exports_Derived_From_Proof_Ins  --
   -------------------------------------------

   procedure Find_Exports_Derived_From_Proof_Ins
     (FA : in out Flow_Analysis_Graphs)
   is
      function Path_Leading_To_Proof_In_Dependency
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id)
        return Vertex_Sets.Set;
      --  Returns a set of vertices that highlight the path in the CFG
      --  where the export depends on a Proof_In.

      ------------------------------------------
      --  Path_Leading_To_Proof_In_Dependency --
      ------------------------------------------

      function Path_Leading_To_Proof_In_Dependency
        (From : Flow_Graphs.Vertex_Id;
         To   : Flow_Graphs.Vertex_Id)
        return Vertex_Sets.Set
      is
         function Vertices_Between_From_And_To
           (From      : Flow_Graphs.Vertex_Id;
            To        : Flow_Graphs.Vertex_Id;
            CFG_Graph : Boolean := False)
           return Vertex_Sets.Set;
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
            CFG_Graph : Boolean := False)
           return Vertex_Sets.Set
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
                       FA.PDG.Get_Vertex (Change_Variant (Input,
                                                          Initial_Value));
                     Tracefile      : Unbounded_String;
                     Vertices_Trail : Vertex_Sets.Set;
                  begin
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.PDG.Get_Attributes (V).Mode = Mode_Proof
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
                           Tag       => "export_depends_on_proof_in");

                        Vertices_Trail := Path_Leading_To_Proof_In_Dependency
                          (From => V,
                           To   => FA.PDG.Get_Vertex (Change_Variant
                                                        (Output,
                                                         Final_Value)));

                        Write_Vertex_Set
                          (G        => FA.PDG,
                           Set      => Vertices_Trail,
                           Filename => To_String (Tracefile));
                     end if;
                  end;
               end loop;
            end if;

         end;
      end loop;
   end Find_Exports_Derived_From_Proof_Ins;

   ---------------------
   -- Check_Contracts --
   ---------------------

   procedure Check_Contracts (FA : in out Flow_Analysis_Graphs) is
      Tracefile : Unbounded_String;

      function Find_Export (E : Entity_Id) return Node_Id;
      --  Looks through the depends aspect on FA.Analyzed_Entity and
      --  returns the node which represents E in the dependency for E.
      --  If none can be found, returns FA.Analyzed_Entity as a
      --  fallback.

      -----------------
      -- Find_Export --
      -----------------

      function Find_Export (E : Entity_Id) return Node_Id
      is
         Depends_Contract : Node_Id;
         Needle           : Node_Id := Empty;

         function Proc (N : Node_Id) return Traverse_Result;
         --  Searches dependency aspect for export E and sets needle
         --  to the node, if found.

         function Proc (N : Node_Id) return Traverse_Result is
            Tmp : Node_Id;
         begin
            case Nkind (N) is
               when N_Component_Association =>
                  Tmp := First (Choices (N));
                  while Present (Tmp) loop
                     if Entity (Tmp) = E then
                        Needle := Tmp;
                        return Abandon;
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

      --  If the user depds do not include something we have in the
      --  actual deps we will raise an appropriate error. We should
      --  however also sanity check there is nothing in the user
      --  dependencies which is *not* in the actual dependencies.

      for C in User_Deps.Iterate loop
         declare
            F_Out : constant Flow_Id := Dependency_Maps.Key (C);
         begin
            if not Actual_Deps.Contains (F_Out) then
               --  ??? check quotation in errout.ads
               Error_Msg_Flow
                 (FA        => FA,
                  Tracefile => Tracefile,
                  Msg       => "missing dependency ""null => #""",
                  N         => Depends_Location,
                  F1        => F_Out,
                  Tag       => "depends_null",
                  Warning   => True);
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
                 (FA        => FA,
                  Tracefile => Tracefile,
                  Msg       => "expected to see & on the left-hand-side of" &
                    " a dependency relation",
                  N         => Depends_Location,
                  F1        => F_Out,
                  Tag       => "depends_missing_clause",
                  Warning   => True);
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
                       FA.PDG.Get_Vertex (Change_Variant (Missing_Var,
                                                          Initial_Value));
                  begin
                     if V /= Flow_Graphs.Null_Vertex
                       and then FA.PDG.Get_Attributes (V).Mode = Mode_Proof
                     then
                        null;
                     else
                        --  Something that the user dependency fails to
                        --  mention.
                        if F_Out = Null_Flow_Id then
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "missing dependency ""null => #""",
                              N         => Depends_Location,
                              F1        => Missing_Var,
                              Tag       => "depends_null",
                              Warning   => True);
                        else
                           Error_Msg_Flow
                             (FA        => FA,
                              Tracefile => Tracefile,
                              Msg       => "missing dependency ""# => #""",
                              N         => Find_Export
                                (Get_Direct_Mapping_Id (F_Out)),
                              F1        => F_Out,
                              F2        => Missing_Var,
                              Tag       => "depends_missing",
                              Warning   => True);
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
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "incorrect dependency ""null => #""",
                        N         => Depends_Location,
                        F1        => Wrong_Var,
                        Tag       => "depends_wrong",
                        Warning   => True);
                     --  ??? show a path?
                  else
                     Error_Msg_Flow
                       (FA        => FA,
                        Tracefile => Tracefile,
                        Msg       => "incorrect dependency ""# => #""",
                        N         => Find_Export
                          (Get_Direct_Mapping_Id (F_Out)),
                        F1        => F_Out,
                        F2        => Wrong_Var,
                        Tag       => "depends_wrong",
                        Warning   => True);
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
      Tracefile : Unbounded_String;

      function Find_Entity (E    : Entity_Id;
                            E_In : Entity_Id := Empty)
                            return Node_Id;
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
        (From : Flow_Graphs.Vertex_Id;
         To   : Vertex_Sets.Set);
      --  This procedure finds the shortest path connecting vertex
      --  From and any vertex contained in To. It then writes a
      --  tracefile containing all vertices in between (From
      --  and To excluded).

      -----------------
      -- Find_Entity --
      -----------------

      function Find_Entity (E    : Entity_Id;
                            E_In : Entity_Id := Empty)
                            return Node_Id
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
            Tmp.Insert (FA.PDG.Get_Vertex
                          (Change_Variant (F, Final_Value)));
         end loop;

         return Tmp;
      end Flow_Id_Set_To_Vertex_Set;

      ---------------------
      -- Write_Tracefile --
      ---------------------

      procedure Write_Tracefile
        (From : Flow_Graphs.Vertex_Id;
         To   : Vertex_Sets.Set)
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
         FA.PDG.Shortest_Path (Start         => From,
                               Allow_Trivial => False,
                               Search        => Are_We_There_Yet'Access,
                               Step          => Add_Loc'Access);

         --  A little sanity check can't hurt.
         pragma Assert (Path_Found);

         Write_Vertex_Set (G        => FA.PDG,
                           Set      => Path,
                           Filename => To_String (Tracefile));
      end Write_Tracefile;

   begin  --  Check_Initializes_Contract
      if not Present (FA.Initializes_N)
        or else not Is_Library_Level_Entity (FA.Analyzed_Entity)
      then
         --  If there is no Initializes contract or if we are not analyzing
         --  a  library level entity then we have nothing to do.
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
                     Tracefile => Tracefile,
                     Msg       => "# must be initialized at elaboration",
                     N         => Find_Entity
                       (E    => Get_Direct_Mapping_Id (The_Out),
                        E_In => Get_Direct_Mapping_Id (G)),
                     F1        => G,
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
               if not All_Contract_Ins.Contains (Actual_In) then
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => "initialization of # must not depend on #",
                     SRM_Ref   => "7.1.5(11)",
                     N         => Find_Entity
                       (Get_Direct_Mapping_Id (The_Out)),
                     F1        => The_Out,
                     F2        => Actual_In,
                     Tag       => "initializes_wrong",
                     Warning   => True);

                  --  Generate and write the tracefile
                  Write_Tracefile
                    (From => FA.PDG.Get_Vertex
                       (Change_Variant (Actual_In, Initial_Value)),
                     To   => Flow_Id_Set_To_Vertex_Set (All_Contract_Outs));
               end if;
            end loop;

            --  Raise warnings for inputs mentioned in the Initializes
            --  that are not actual inputs.
            for Contract_In of All_Contract_Ins loop
               if not All_Actual_Ins.Contains (Contract_In) then
                  Error_Msg_Flow
                    (FA        => FA,
                     Tracefile => Tracefile,
                     Msg       => "initialization of # does not depend on #",
                     SRM_Ref   => "7.1.5(11)",
                     N         => Find_Entity
                       (Get_Direct_Mapping_Id (The_Out)),
                     F1        => The_Out,
                     F2        => Contract_In,
                     Tag       => "initializes_wrong",
                     Warning   => True);
               end if;
            end loop;

         end loop;
      end;
   end Check_Initializes_Contract;

end Flow.Analysis;
