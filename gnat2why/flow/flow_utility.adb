------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         F L O W _ U T I L I T Y                          --
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

with Elists;                 use Elists;
with Errout;                 use Errout;
with Nlists;                 use Nlists;

with Output;                 use Output;
with Sprint;                 use Sprint;
with Treepr;                 use Treepr;
with Flow.Debug;             use Flow.Debug;

with Why;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Definition;       use SPARK_Definition;

with Flow_Tree_Utility;      use Flow_Tree_Utility;

package body Flow_Utility is

   use type Flow_Id_Sets.Set;

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   Debug_Trace_Get_Global : constant Boolean := False;
   --  Enable this to debug Get_Global.

   Debug_Trace_Untangle   : constant Boolean := False;
   --  Enable this to print the tree and def/use sets in each call of
   --  Untangle_Assignment_Target.

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
      with Pre => Ekind (Get_Full_Type (Entire_Var)) in
        E_Record_Type | E_Record_Subtype;
   --  Given the record Entire_Var, return a set with all components.
   --  So, for example we might return:
   --     * p.x
   --     * p.r.a
   --     * p.r.b

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
      with Pre => The_Record_Field.Kind in Direct_Mapping | Record_Field
                  and then Ekind (Get_Full_Type
                                    (Get_Direct_Mapping_Id
                                       (The_Record_Field))) in
                                     E_Record_Type | E_Record_Subtype;
   --  As above but only include fields that are equal to Record_Field or are
   --  nested under it. For example if Record_Field = p.r for the above
   --  record, then we will get the following set:
   --     * p.r.a
   --     * p.r.b

   function Filter_Out_Non_Local_Constants (S : Flow_Id_Sets.Set;
                                            C : Node_Sets.Set)
                                            return Flow_Id_Sets.Set;
   --  Remove all flow_ids referencing constants from the set.

   ---------------------------
   -- All_Record_Components --
   ---------------------------

   function All_Record_Components
     (Entire_Var : Entity_Id)
      return Flow_Id_Sets.Set
   is
   begin
      return All_Record_Components (Direct_Mapping_Id (Entire_Var));
   end All_Record_Components;

   function All_Record_Components
     (The_Record_Field : Flow_Id)
      return Flow_Id_Sets.Set
   is
      Entire_Var : constant Entity_Id :=
        Get_Direct_Mapping_Id (The_Record_Field);

      All_Comp   : Flow_Id_Sets.Set   := Flow_Id_Sets.Empty_Set;

      procedure Possibly_Include (F : Flow_Id);
      --  Include F in All_Comp if it is The_Record_Field or a
      --  subcomponent of it.

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      with Pre => Ekind (R_Type) in E_Record_Type | E_Record_Subtype;
      --  Recursively go through the record's components, adding
      --  everything to All_Comp.

      procedure Possibly_Include (F : Flow_Id)
      is
      begin
         --  ??? Direct access into flow_id, should be removed somehow.
         if F.Component.Length < The_Record_Field.Component.Length then
            return;
         end if;

         for I in Natural
           range 1 .. Natural (The_Record_Field.Component.Length)
         loop
            if The_Record_Field.Component (I) /= F.Component (I) then
               return;
            end if;
         end loop;

         All_Comp.Include (F);
      end Possibly_Include;

      procedure Process_Record (R_Type : Entity_Id;
                                Comp   : Entity_Lists.Vector)
      is
         C : Entity_Id;
         F : Flow_Id;
      begin
         --  Make a vertex for each subcomponent, unless its a
         --  record. If we have a record we recurse instead.
         C := First_Component_Or_Discriminant (R_Type);
         while Present (C) loop
            declare
               Tmp : Entity_Lists.Vector := Comp;
            begin
               Tmp.Append (C);

               case Ekind (Get_Full_Type (C)) is
                  when E_Record_Type =>
                     Process_Record (Get_Full_Type (C), Tmp);

                  when others =>
                     F := Flow_Id'(Kind      => Record_Field,
                                   Variant   => Normal_Use,
                                   Node      => Entire_Var,
                                   Name      => Null_Entity_Name,
                                   Component => Tmp);
                     Possibly_Include (F);
               end case;
            end;

            C := Next_Component_Or_Discriminant (C);
         end loop;
      end Process_Record;

   begin
      Process_Record (Get_Full_Type (Entire_Var),
                      Entity_Lists.Empty_Vector);
      return All_Comp;
   end All_Record_Components;

   --------------------
   -- Find_Contracts --
   --------------------

   function Find_Contracts (E    : Entity_Id;
                            Name : Name_Id)
                            return Node_Lists.List
   is
      C          : constant Node_Id := Contract (E);
      P          : Node_Id;
      Contracts  : Node_Lists.List := Node_Lists.Empty_List;
      Other_Name : Name_Id;
   begin
      case Name is
         when Name_Precondition      |
              Name_Postcondition     |
              Name_Refined_Post      |
              Name_Contract_Cases    |
              Name_Initial_Condition =>

            if Name = Name_Precondition then
               Other_Name := Name_Pre;
               P := Pre_Post_Conditions (C);
            elsif Name = Name_Postcondition then
               Other_Name := Name_Post;
               P := Pre_Post_Conditions (C);
            elsif Name = Name_Refined_Post then
               Other_Name := Name_Refined_Post;
               P := Pre_Post_Conditions
                 (Contract (Defining_Entity (Specification
                                               (Get_Subprogram_Body (E)))));
            elsif Name = Name_Initial_Condition then
               Other_Name := Name_Initial_Condition;
               P := Classifications (C);
            else
               Other_Name := Name_Contract_Cases;
               P := Contract_Test_Cases (C);
            end if;

            while Present (P) loop
               if Chars (Pragma_Identifier (P)) in Name | Other_Name then
                  Contracts.Append
                    (Expression (First (Pragma_Argument_Associations (P))));
               end if;

               P := Next_Pragma (P);
            end loop;

            return Contracts;

         when Name_Global | Name_Depends =>
            raise Why.Not_Implemented;

         when others =>
            raise Program_Error;
      end case;
   end Find_Contracts;

   ------------------------------------
   -- Filter_Out_Non_Local_Constants --
   ------------------------------------

   function Filter_Out_Non_Local_Constants (S : Flow_Id_Sets.Set;
                                            C : Node_Sets.Set)
                                            return Flow_Id_Sets.Set
   is
      R : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for F of S loop
         case F.Kind is
            when Direct_Mapping | Record_Field =>
               declare
                  E : constant Entity_Id := Get_Direct_Mapping_Id (F);
                  pragma Assert (Nkind (E) in N_Entity);
               begin
                  if Ekind (E) /= E_Constant or else C.Contains (E) then
                     R.Include (F);
                  end if;
               end;

            when Magic_String | Synthetic_Null_Export =>
               R.Include (F);

            when Null_Value =>
               raise Program_Error;
         end case;
      end loop;
      return R;
   end Filter_Out_Non_Local_Constants;

   ----------------------------------------------------------------------
   --  Package
   ----------------------------------------------------------------------

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Proof_Ins              : out Flow_Id_Sets.Set;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Consider_Discriminants : Boolean := False;
                          Globals_For_Proof      : Boolean := False)
   is
      Global_Node : constant Node_Id := Get_Contract_Node (Subprogram,
                                                           Scope,
                                                           Global_Contract);
   begin
      Proof_Ins := Flow_Id_Sets.Empty_Set;
      Reads     := Flow_Id_Sets.Empty_Set;
      Writes    := Flow_Id_Sets.Empty_Set;

      if Debug_Trace_Get_Global then
         Write_Str ("Get_Global (");
         Sprint_Node (Subprogram);
         Write_Str (", ");
         Print_Flow_Scope (Scope);
         Write_Str (")");
         Write_Eol;
      end if;

      if Present (Global_Node) then
         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("using user annotation");
            Write_Eol;
            Outdent;
         end if;

         declare
            pragma Assert
              (List_Length (Pragma_Argument_Associations (Global_Node)) = 1);

            PAA : constant Node_Id :=
              First (Pragma_Argument_Associations (Global_Node));
            pragma Assert (Nkind (PAA) = N_Pragma_Argument_Association);

            Row      : Node_Id;
            The_Mode : Name_Id;
            RHS      : Node_Id;

            G_Proof : Node_Sets.Set := Node_Sets.Empty_Set;
            G_In    : Node_Sets.Set := Node_Sets.Empty_Set;
            G_Out   : Node_Sets.Set := Node_Sets.Empty_Set;

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id);
            --  Add the given global to the reads or writes list,
            --  depending on the mode.

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            is
            begin
               case The_Mode is
                  when Name_Input =>
                     if not Globals_For_Proof or else
                       Ekind (The_Global) /= E_In_Parameter
                     then
                        --  Proof does not count in parameters as
                        --  globals (as they are constants).
                        G_In.Insert (The_Global);
                     end if;

                  when Name_In_Out =>
                     G_In.Insert (The_Global);
                     G_Out.Insert (The_Global);

                  when Name_Output =>
                     if Consider_Discriminants and then
                       Contains_Discriminants
                       (Direct_Mapping_Id (The_Global, In_View))
                     then
                        G_In.Insert (The_Global);
                     end if;
                     G_Out.Insert (The_Global);

                  when Name_Proof_In =>
                     if not Globals_For_Proof or else
                       Ekind (The_Global) /= E_In_Parameter
                     then
                        --  See above.
                        G_Proof.Insert (The_Global);
                     end if;

                  when others =>
                     raise Program_Error;
               end case;
            end Process;
         begin

            ---------------------------------------------------------------
            --  Step 1: Process global annotation, filling in g_proof,
            --  g_in, and g_out.
            ---------------------------------------------------------------

            if Nkind (Expression (PAA)) = N_Null then
               --  global => null
               --  No globals, nothing to do.
               return;

            elsif Nkind (Expression (PAA)) in
              N_Identifier | N_Expanded_Name
            then
               --  global => foo
               --  A single input
               Process (Name_Input, Entity (Expression (PAA)));

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Expressions (Expression (PAA)) /= No_List
            then
               --  global => (foo, bar)
               --  Inputs
               RHS := First (Expressions (Expression (PAA)));
               while Present (RHS) loop
                  case Nkind (RHS) is
                     when N_Identifier | N_Expanded_Name =>
                        Process (Name_Input, Entity (RHS));
                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
                  RHS := Next (RHS);
               end loop;

            elsif Nkind (Expression (PAA)) = N_Aggregate and then
              Component_Associations (Expression (PAA)) /= No_List
            then
               --  global => (mode => foo,
               --             mode => (bar, baz))
               --  A mixture of things.

               declare
                  CA : constant List_Id :=
                    Component_Associations (Expression (PAA));
               begin
                  Row := First (CA);
                  while Present (Row) loop
                     pragma Assert (List_Length (Choices (Row)) = 1);
                     The_Mode := Chars (First (Choices (Row)));

                     RHS := Expression (Row);
                     case Nkind (RHS) is
                        when N_Aggregate =>
                           RHS := First (Expressions (RHS));
                           while Present (RHS) loop
                              Process (The_Mode, Entity (RHS));
                              RHS := Next (RHS);
                           end loop;
                        when N_Identifier | N_Expanded_Name =>
                           Process (The_Mode, Entity (RHS));
                        when N_Null =>
                           null;
                        when others =>
                           Print_Node_Subtree (RHS);
                           raise Why.Unexpected_Node;
                     end case;

                     Row := Next (Row);
                  end loop;
               end;

            else
               raise Why.Unexpected_Node;
            end if;

            ---------------------------------------------------------------
            --  Step 2: Expand any abstract state that might be too refined
            --  for our given scope.
            ---------------------------------------------------------------

            G_Proof := Down_Project (G_Proof, Scope);
            G_In    := Down_Project (G_In,    Scope);
            G_Out   := Down_Project (G_Out,   Scope);

            ---------------------------------------------------------------
            --  Step 3: Sanity check that none of the proof ins are
            --  mentioned as ins.
            ---------------------------------------------------------------

            --  pragma Assert ((G_Proof and G_In) = Node_Sets.Empty_Set);

            ---------------------------------------------------------------
            --  Step 4: Convert to a Flow_Id set.
            ---------------------------------------------------------------

            for V of G_Proof loop
               Proof_Ins.Include (Direct_Mapping_Id (V, In_View));
            end loop;
            for V of G_In loop
               Reads.Include (Direct_Mapping_Id (V, In_View));
            end loop;
            for V of G_Out loop
               Writes.Include (Direct_Mapping_Id (V, Out_View));
            end loop;

         end;
      else
         --  We don't have a global aspect, so we should look at the
         --  computed globals...

         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("using computed globals");
            Write_Eol;
            Outdent;
         end if;

         declare
            function Get_Flow_Id
              (Name : Entity_Name;
               View : Parameter_Variant)
               return Flow_Id;
            --  Return a suitable flow id for the unique_name of an
            --  entity. We try our best to get a direct mapping,
            --  resorting to the magic string only as a last resort.

            function Get_Flow_Id
              (Name : Entity_Name;
               View : Parameter_Variant)
               return Flow_Id is
               E : constant Entity_Id := Find_Object_Entity (Name);
            begin
               if Present (E) then
                  return Direct_Mapping_Id (E, View);
               end if;

               --  If none can be found, we fall back to the magic
               --  string.
               return Magic_String_Id (Name, View);
            end Get_Flow_Id;

            ALI_Reads  : constant Name_Set.Set :=
              Get_Generated_Reads (Subprogram,
                                   Include_Constants => not Globals_For_Proof);
            ALI_Writes : constant Name_Set.Set :=
              Get_Generated_Writes (Subprogram);

            F : Flow_Id;
         begin

            --  We process the reads
            if Debug_Trace_Get_Global then
               Indent;
               Write_Str ("reads");
               Write_Eol;
               Indent;
            end if;

            for R of ALI_Reads loop
               F := Get_Flow_Id (R, In_View);

               if Debug_Trace_Get_Global then
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end if;

               case F.Kind is
                  when Direct_Mapping =>
                     if Ekind (Get_Direct_Mapping_Id (F)) /= E_Constant then
                        --  We completely ignore all non-local constants
                        --  for now.
                        Reads.Include (F);
                     end if;

                  when Magic_String =>
                     Reads.Include (F);

                  when Null_Value | Record_Field | Synthetic_Null_Export  =>
                     raise Program_Error;
               end case;
            end loop;

            if Debug_Trace_Get_Global then
               Outdent;
               Write_Str ("writes");
               Write_Eol;
               Indent;
            end if;

            for W of ALI_Writes loop
               --  This is not a mistake, we must assume that all
               --  values written may also not change or that they are
               --  only partially updated.
               --
               --  This also takes care of discriminants as every out
               --  is really an in out.
               F := Get_Flow_Id (W, Out_View);

               if Debug_Trace_Get_Global then
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end if;

               Reads.Include (Change_Variant (F, In_View));
               Writes.Include (F);
            end loop;

            if Debug_Trace_Get_Global then
               Outdent;
               Outdent;
            end if;
         end;

      end if;

   end Get_Globals;

   -----------------------
   -- Get_Proof_Globals --
   -----------------------

   procedure Get_Proof_Globals (Subprogram : Entity_Id;
                                Reads      : out Flow_Id_Sets.Set;
                                Writes     : out Flow_Id_Sets.Set)
   is
      Proof_Ins : Flow_Id_Sets.Set;
      Tmp_In    : Flow_Id_Sets.Set;
      Tmp_Out   : Flow_Id_Sets.Set;
      Body_E    : constant Entity_Id := Get_Body (Subprogram);

      function Expand (F : Flow_Id) return Flow_Id_Sets.Set;
      --  If F represents abstract state, return the set of all its
      --  components. Otherwise return F.

      ------------
      -- Expand --
      ------------

      function Expand (F : Flow_Id) return Flow_Id_Sets.Set
      is
         Tmp : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         Ptr : Elmt_Id;
      begin
         case F.Kind is
            when Direct_Mapping =>
               case Ekind (Get_Direct_Mapping_Id (F)) is
                  when E_Abstract_State =>
                     Ptr := First_Elmt (Refinement_Constituents
                                          (Get_Direct_Mapping_Id (F)));
                     while Present (Ptr) loop
                        Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                              F.Variant)));
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     Ptr := First_Elmt (Part_Of_Constituents
                                          (Get_Direct_Mapping_Id (F)));
                     while Present (Ptr) loop
                        Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                              F.Variant)));
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     if Tmp.Is_Empty then
                        --  If we can't refine this state (maybe the body
                        --  is not in SPARK, or simply not implemented)
                        --  then we use the abstract state itself.
                        Tmp.Insert (F);
                     end if;

                  when others =>
                     Tmp.Insert (F);
               end case;

            when Magic_String =>
               Tmp.Insert (F);

            when Record_Field | Null_Value | Synthetic_Null_Export =>
               raise Program_Error;
         end case;
         return Tmp;
      end Expand;

   begin
      Get_Globals
        (Subprogram             => Subprogram,
         Scope                  => (if Present (Body_E) and then
                                      Entity_Body_In_SPARK (Subprogram)
                                    then Get_Flow_Scope (Body_E)
                                    else Get_Flow_Scope (Subprogram)),
         Proof_Ins              => Proof_Ins,
         Reads                  => Tmp_In,
         Writes                 => Tmp_Out,
         Consider_Discriminants => False,
         Globals_For_Proof      => True);

      --  Merge the proof ins with the reads.
      Tmp_In.Union (Proof_Ins);

      --  Expand all variables.
      Reads := Flow_Id_Sets.Empty_Set;
      for F of Tmp_In loop
         Reads.Union (Expand (F));
      end loop;

      Writes := Flow_Id_Sets.Empty_Set;
      for F of Tmp_Out loop
         Writes.Union (Expand (F));
      end loop;
   end Get_Proof_Globals;

   ----------------------------
   -- Has_Proof_Global_Reads --
   ----------------------------

   function Has_Proof_Global_Reads (Subprogram : Entity_Id) return Boolean
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      Get_Proof_Globals (Subprogram => Subprogram,
                         Reads      => Read_Ids,
                         Writes     => Write_Ids);
      return not Read_Ids.Is_Empty;
   end Has_Proof_Global_Reads;

   -----------------------------
   -- Has_Proof_Global_Writes --
   -----------------------------

   function Has_Proof_Global_Writes (Subprogram : Entity_Id) return Boolean
   is
      Read_Ids  : Flow_Types.Flow_Id_Sets.Set;
      Write_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      Get_Proof_Globals (Subprogram => Subprogram,
                         Reads      => Read_Ids,
                         Writes     => Write_Ids);
      return not Write_Ids.Is_Empty;
   end Has_Proof_Global_Writes;

   ------------------------
   --  Get_Variable_Set  --
   ------------------------

   function Get_Variable_Set
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;

      procedure Process_Subprogram_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set)
         with Pre => Nkind (Callsite) in N_Subprogram_Call;
      --  Work out which variables (including globals) are used in the
      --  function call and add them to the given set.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Adds each identifier or defining_identifier found to VS, as
      --  long as we are dealing with:
      --     * a variable
      --     * a subprogram parameter
      --     * a loop parameter
      --     * a constant

      ---------------------------
      -- Process_Function_Call --
      ---------------------------

      procedure Process_Subprogram_Call
        (Callsite       : Node_Id;
         Used_Variables : in out Flow_Id_Sets.Set)
      is

         Subprogram    : constant Entity_Id := Entity (Name (Callsite));

         Proof_Reads   : Flow_Id_Sets.Set;
         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;
      begin
         Get_Globals (Subprogram   => Subprogram,
                      Scope        => Scope,
                      Proof_Ins    => Proof_Reads,
                      Reads        => Global_Reads,
                      Writes       => Global_Writes);
         Global_Reads.Union (Proof_Reads);

         if Nkind (Callsite) = N_Function_Call and then
           Flow_Id_Sets.Length (Global_Writes) > 0
         then
            Error_Msg_NE
              (Msg => "side-effects of function & are not modelled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Forming the set of variables for a parameter list never involves
         --  a statement, so we can recurse with Allow_Statements => False here
         Used_Variables.Union
           (Get_Variable_Set
              (Parameter_Associations (Callsite),
               Scope                        => Scope,
               Local_Constants              => Local_Constants,
               Reduced                      => Reduced,
               Allow_Statements             => False,
               Expand_Synthesized_Constants => Expand_Synthesized_Constants));

         for G of Global_Reads loop
            for F of Flatten_Variable (G) loop
               Used_Variables.Include (Change_Variant (F, Normal_Use));
            end loop;
         end loop;
      end Process_Subprogram_Call;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Procedure_Call_Statement =>
               if not Allow_Statements then
                  --  If we ever get one of these we have a problem -
                  --  Get_Variable_Set is only really meant to be
                  --  called on expressions and not statements.
                  raise Program_Error;

               else
                  Process_Subprogram_Call (Callsite       => N,
                                           Used_Variables => VS);
                  return Skip;
               end if;

            when N_Later_Decl_Item =>
               --  These should allow us to go through package specs
               --  and bodies.
               return Skip;

            when N_Function_Call =>
               Process_Subprogram_Call (Callsite       => N,
                                        Used_Variables => VS);
               return Skip;

            when N_Identifier | N_Expanded_Name =>
               if Present (Entity (N)) then
                  case Ekind (Entity (N)) is
                     when E_Constant =>
                        if Expand_Synthesized_Constants and then
                          not Comes_From_Source (Entity (N))
                        then
                           --  To expand synthesized constants, we need to find
                           --  the original expression and find the variable
                           --  set of that.
                           declare
                              Obj_Decl : constant Node_Id :=
                                Parent (Entity (N));
                              E        : constant Node_Id :=
                                Expression (Obj_Decl);
                           begin
                              pragma Assert
                                (Nkind (Obj_Decl) =
                                   N_Object_Declaration,
                                 "Bad parent of constant entity");
                              pragma Assert
                                (Present (E),
                                 "Constant has no expression");
                              VS.Union
                                (Get_Variable_Set
                                   (N                            => E,
                                    Scope                        => Scope,
                                    Local_Constants              =>
                                      Local_Constants,
                                    Reduced                      => Reduced,
                                    Allow_Statements             =>
                                      Allow_Statements,
                                    Expand_Synthesized_Constants =>
                                      Expand_Synthesized_Constants));
                           end;

                        else
                           --  If this constant comes from source, and
                           --  it's in Local_Constants, then add it.
                           if Local_Constants.Contains (Entity (N)) then
                              if Reduced then
                                 VS.Include (Direct_Mapping_Id
                                             (Unique_Entity (Entity (N))));
                              else
                                 VS.Union (Flatten_Variable (Entity (N)));
                              end if;
                           end if;

                        end if;

                     when E_Variable |
                       E_Loop_Parameter |
                       E_Out_Parameter |
                       E_In_Parameter |
                       E_In_Out_Parameter =>

                        if Reduced then
                           VS.Include (Direct_Mapping_Id
                                       (Unique_Entity (Entity (N))));
                        else
                           VS.Union (Flatten_Variable (Entity (N)));
                        end if;
                     when others =>
                        null;
                  end case;
               end if;

            when N_Defining_Identifier =>
               case Ekind (N) is
                  when E_Constant |
                    E_Variable |
                    E_Loop_Parameter |
                    E_Out_Parameter |
                    E_In_Parameter |
                    E_In_Out_Parameter =>
                     if Ekind (N) /= E_Constant or else
                       Local_Constants.Contains (N)
                     then
                        if Reduced then
                           VS.Include (Direct_Mapping_Id (Unique_Entity (N)));
                        else
                           VS.Union (Flatten_Variable (N));
                        end if;
                     end if;
                  when others =>
                     null;
               end case;

            when N_Selected_Component | N_Indexed_Component =>

               if Reduced then

                  --  In reduced mode we just keep traversing the
                  --  tree.

                  return OK;

               elsif not Contains_Loop_Entry_Reference (N) then

                  --  We strip out loop entry references as they are
                  --  dealt with by Do_Pragma and Do_Loop_Statement in
                  --  the CFG construction.

                  --  We use Untangle here because that takes care of
                  --  individual record fields.

                  declare
                     A, B, C : Flow_Id_Sets.Set;
                  begin
                     Untangle_Assignment_Target
                       (N                    => N,
                        Scope                => Scope,
                        Local_Constants      => Local_Constants,
                        Vars_Explicitly_Used => A,
                        Vars_Implicitly_Used => B,
                        Vars_Defined         => C);
                     VS.Union (A);
                     VS.Union (B);
                     VS.Union (C);
                  end;
                  return Skip;

               else

                  return Skip;

               end if;

            when N_Attribute_Reference =>
               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_First |
                    Attribute_Last |
                    Attribute_Length |
                    Attribute_Range =>
                     --  Ignore anything to do with ranges.
                     return Skip;

                  when Attribute_Loop_Entry =>
                     --  Again, we ignore loop entry references, these
                     --  are dealt with by Do_Pragma and
                     --  Do_Loop_Statement in the CFG construction.
                     return Skip;

                  when others =>
                     null;
               end case;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

   --  Start of Get_Variable_Set

   begin
      Traverse (N);
      return Filter_Out_Non_Local_Constants (VS, Local_Constants);
   end Get_Variable_Set;

   function Get_Variable_Set
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;
      P  : Node_Id;
   begin
      P := First (L);
      while Present (P) loop
         VS.Union
           (Get_Variable_Set
              (N                            => P,
               Scope                        => Scope,
               Local_Constants              => Local_Constants,
               Reduced                      => Reduced,
               Allow_Statements             => Allow_Statements,
               Expand_Synthesized_Constants => Expand_Synthesized_Constants));

         P := Next (P);
      end loop;
      return VS;
   end Get_Variable_Set;

   --------------------------
   -- Quantified_Variables --
   --------------------------

   function Quantified_Variables (N : Node_Id) return Flow_Id_Sets.Set is
      RV : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;

      function Proc (N : Node_Id) return Traverse_Result;

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Quantified_Expression =>
               if Present (Iterator_Specification (N)) then
                  RV.Include (Direct_Mapping_Id
                                (Defining_Identifier
                                   (Iterator_Specification (N))));
               elsif Present (Loop_Parameter_Specification (N)) then
                  RV.Include (Direct_Mapping_Id
                                (Defining_Identifier
                                   (Loop_Parameter_Specification (N))));
               else
                  Print_Tree_Node (N);
                  raise Why.Unexpected_Node;
               end if;

            when others =>
               null;
         end case;
         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Proc);
   begin
      Traverse (N);
      return RV;
   end Quantified_Variables;

   ----------------------
   -- Flatten_Variable --
   ----------------------

   function Flatten_Variable (E : Entity_Id) return Flow_Id_Sets.Set is
      U : constant Entity_Id := Unique_Entity (E);
   begin
      case Ekind (Get_Full_Type (U)) is
         when Elementary_Kind | Array_Kind | Private_Kind =>
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (U));

         when E_Record_Type | E_Record_Subtype =>
            return All_Record_Components (Entire_Var => U);

         when E_Void =>
            pragma Assert (Ekind (E) = E_Abstract_State);
            return Flow_Id_Sets.To_Set (Direct_Mapping_Id (U));

         when others =>
            Print_Tree_Node (U);
            Print_Tree_Node (Etype (U));
            raise Why.Unexpected_Node;
      end case;
   end Flatten_Variable;

   function Flatten_Variable (F : Flow_Id) return Flow_Id_Sets.Set is
   begin
      case F.Kind is
         when Direct_Mapping =>
            return Flatten_Variable (Get_Direct_Mapping_Id (F));
         when Magic_String | Synthetic_Null_Export =>
            return Flow_Id_Sets.To_Set (F);
         when others =>
            raise Program_Error;
      end case;
   end Flatten_Variable;

   -------------------
   -- Get_Full_Type --
   -------------------

   function Get_Full_Type (E : Entity_Id) return Entity_Id
   is
      T : constant Entity_Id := Etype (E);
   begin
      if Ekind (E) = E_Abstract_State then
         return T;
      else
         pragma Assert (Is_Type (T));
         if Present (Full_View (T)) then
            return Full_View (T);
         else
            return T;
         end if;
      end if;
   end Get_Full_Type;

   --------------------------------
   -- Untangle_Assignment_Target --
   --------------------------------

   procedure Untangle_Assignment_Target
     (N                    : Node_Id;
      Scope                : Flow_Scope;
      Local_Constants      : Node_Sets.Set;
      Vars_Defined         : out Flow_Id_Sets.Set;
      Vars_Explicitly_Used : out Flow_Id_Sets.Set;
      Vars_Implicitly_Used : out Flow_Id_Sets.Set)
   is
      procedure Find_Bottom_Node (N             : Node_Id;
                                  Bottom_Node   : out Node_Id;
                                  End_Of_Record : out Node_Id;
                                  Partial_Use   : out Boolean);
      --  This procedure returns the bottom node of the subtree and
      --  finds the end of the outermost record node. We also detect
      --  if the end of record node is a partial use (array indexing)
      --  or entire use.
      --
      --  Let's consider the parse tree for P.R.A (I).A (J).X
      --  In the following parse tree 'i' represents an indexed
      --  component and s represents a selected component.
      --
      --                               Parse Tree
      --                                    s
      --                                   / \
      --                                  i   X
      --                                 / \
      --                                s   J
      --                               / \
      --                              i   A
      --                             / \
      --        End_Of_Record --->  s   I
      --                           / \
      --                          s   A
      --                         / \
      --      Bottom_Node --->  P   R
      --
      --  In this example Partial_Use would be True. If we had been
      --  given only P.R.A Partial_Use would be False.

      function Proc (N : Node_Id) return Traverse_Result;
      --  Traverses a subtree and adds each variable found inside
      --  the expression part of an N_Indexed_Component to the
      --  Vars_Used set.

      -------------------
      -- Find_Top_Node --
      -------------------

      procedure Find_Bottom_Node
        (N             : Node_Id;
         Bottom_Node   : out Node_Id;
         End_Of_Record : out Node_Id;
         Partial_Use   : out Boolean)
      is
      begin
         Bottom_Node   := N;
         End_Of_Record := N;
         Partial_Use   := False;

         while Nkind (Bottom_Node) in
           N_Indexed_Component | N_Selected_Component |
           N_Slice | N_Type_Conversion
         loop
            if Nkind (Bottom_Node) in N_Indexed_Component | N_Slice then
               End_Of_Record := Prefix (Bottom_Node);
               Partial_Use   := True;
            end if;
            Bottom_Node := Prefix (Bottom_Node);
         end loop;
      end Find_Bottom_Node;

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         case Nkind (N) is
            when N_Indexed_Component | N_Attribute_Reference =>
               Vars_Explicitly_Used.Union
                 (Get_Variable_Set
                    (Expressions (N),
                     Scope           => Scope,
                     Local_Constants => Local_Constants));
               return OK;
            when N_Slice =>
               Vars_Explicitly_Used.Union
                 (Get_Variable_Set
                    (Discrete_Range (N),
                     Scope           => Scope,
                     Local_Constants => Local_Constants));
               return OK;
            when others =>
               return OK;
         end case;
      end Proc;

      procedure Merge_Array_Expressions is new Traverse_Proc (Proc);

      Bottom_Node   : Node_Id;
      End_Of_Record : Node_Id;
      Partial_Use   : Boolean;

   begin
      Vars_Defined         := Flow_Id_Sets.Empty_Set;
      Vars_Explicitly_Used := Flow_Id_Sets.Empty_Set;
      Vars_Implicitly_Used := Flow_Id_Sets.Empty_Set;

      if Debug_Trace_Untangle then
         Sprint_Node (N);
         Print_Node_Subtree (N);
      end if;

      case Nkind (N) is
         when N_Type_Conversion =>
            Untangle_Assignment_Target
              (N                    => Expression (N),
               Scope                => Scope,
               Local_Constants      => Local_Constants,
               Vars_Defined         => Vars_Defined,
               Vars_Explicitly_Used => Vars_Explicitly_Used,
               Vars_Implicitly_Used => Vars_Implicitly_Used);

         when N_Identifier | N_Expanded_Name =>
            --  X :=
            Vars_Defined := Get_Variable_Set (N, Scope, Local_Constants);

         when N_Selected_Component | N_Indexed_Component | N_Slice =>
            --  R.A :=
            --  A (...) :=

            --  First we collect all variables used in any index
            --  expression or a slice range, as they are always used.
            --
            --  So out of A (X + B (Y)).B (I) we call Get_Variable_Set
            --  on X + B (Y) and I and add this to Vars_Used.

            Merge_Array_Expressions (N);

            --  We now need to work out what we're ultimately dealing
            --  with. Bottom_Node is the entire variable and
            --  End_Of_Record points to either the entire variable or
            --  the last N_Selected_Component flow analysis will care
            --  about.

            Find_Bottom_Node (N, Bottom_Node, End_Of_Record, Partial_Use);

            --  We may be dealing with some record field. For example:
            --
            --     R.A
            --     R.A (12)
            --     R.A (12).Specific_Field
            --
            --  In all of these End_Of_Record will point to R.A.
            --
            --  There is the possibility that we are still dealing
            --  with more than one variable, for example if R.X.A and
            --  R.X.B exist then R.X will deal with both of the above.
            --
            --  We are interested it what comes next. For example with
            --  R.A we just define R.A, but with R.A (12) we define
            --  and use it. The Partial_Use flag keeps track of this.

            case Nkind (End_Of_Record) is
               when N_Selected_Component =>
                  case Nkind (Prefix (End_Of_Record)) is
                     when N_Function_Call =>
                        Vars_Defined.Union
                          (Get_Variable_Set
                             (Prefix (End_Of_Record),
                              Scope           => Scope,
                              Local_Constants => Local_Constants));

                     when N_Unchecked_Type_Conversion =>
                        --  This is an interesting special case. We
                        --  are querying a specific record field of
                        --  the result of an unchecked conversion. The
                        --  variables used and defined should be the
                        --  argument to the unchecked conversion.
                        Vars_Defined.Union
                          (Get_Variable_Set
                             (Expression (Prefix (End_Of_Record)),
                              Scope           => Scope,
                              Local_Constants => Local_Constants));

                        --  Since we are using the defined variable
                        --  only partially, we need to make sure its
                        --  also used.
                        Vars_Implicitly_Used.Union (Vars_Defined);

                     when others =>
                        Vars_Defined.Union
                          (All_Record_Components
                             (Record_Field_Id (End_Of_Record)));
                        if Partial_Use then
                           Vars_Implicitly_Used.Union
                             (All_Record_Components
                                (Record_Field_Id (End_Of_Record)));
                        end if;
                  end case;

               when N_Indexed_Component | N_Slice =>
                  raise Program_Error;

               when N_Function_Call =>
                  --  Not strictly right, but this will satisfy the
                  --  postcondition.
                  Vars_Defined.Union (Get_Variable_Set
                                        (End_Of_Record,
                                         Scope           => Scope,
                                         Local_Constants => Local_Constants));

               when N_Unchecked_Type_Conversion =>
                  --  See above.
                  Vars_Defined.Union (Get_Variable_Set
                                        (Expression (End_Of_Record),
                                         Scope           => Scope,
                                         Local_Constants => Local_Constants));

               when N_Attribute_Reference =>
                  declare
                     P : Node_Id := End_Of_Record;
                  begin
                     while Nkind (P) = N_Attribute_Reference loop
                        P := Prefix (P);
                     end loop;
                     Vars_Defined.Include
                       (Direct_Mapping_Id (Entity (P)));
                     if Partial_Use then
                        Vars_Implicitly_Used.Include
                          (Direct_Mapping_Id (Entity (P)));
                     end if;
                  end;

               when others =>
                  Vars_Defined.Include
                    (Direct_Mapping_Id (Entity (End_Of_Record)));
                  if Partial_Use then
                     Vars_Implicitly_Used.Include
                       (Direct_Mapping_Id (Entity (End_Of_Record)));
                  end if;
            end case;

         when others =>
            raise Why.Unexpected_Node;
      end case;

      if Debug_Trace_Untangle then
         Print_Node_Set (Vars_Explicitly_Used);
         Print_Node_Set (Vars_Implicitly_Used);
         Print_Node_Set (Vars_Defined);
      end if;
   end Untangle_Assignment_Target;

   ----------------------------------
   -- Get_Precondition_Expressions --
   ----------------------------------

   function Get_Precondition_Expressions (E : Entity_Id)
                                          return Node_Lists.List
   is
      Precondition_Expressions : Node_Lists.List :=
        Find_Contracts (E, Name_Precondition);
      Contract_Case            : constant Node_Lists.List :=
        Find_Contracts (E, Name_Contract_Cases);
   begin
      --  If a Contract_Cases aspect was found then we pull out every
      --  condition apart from the others.
      if not Contract_Case.Is_Empty then
         declare
            C_Case    : Node_Id;
            Condition : Node_Id;
         begin
            C_Case := First (Component_Associations
                               (Contract_Case.First_Element));
            while Present (C_Case) loop
               Condition := First (Choices (C_Case));
               if Nkind (Condition) /= N_Others_Choice then
                  Precondition_Expressions.Append (Condition);
               end if;

               C_Case := Next (C_Case);
            end loop;
         end;
      end if;

      return Precondition_Expressions;

   end Get_Precondition_Expressions;

   -----------------------------------
   -- Get_Postcondition_Expressions --
   -----------------------------------

   function Get_Postcondition_Expressions (E       : Entity_Id;
                                           Refined : Boolean)
                                           return Node_Lists.List
   is
      P_Expr : Node_Lists.List;
      P_CC   : Node_Lists.List;
   begin
      case Ekind (E) is
         when Subprogram_Kind =>
            if Refined then
               P_Expr := Find_Contracts (E, Name_Refined_Post);
            else
               P_Expr := Find_Contracts (E, Name_Postcondition);
               P_CC   := Find_Contracts (E, Name_Contract_Cases);

               --  If a Contract_Cases aspect was found then we pull out
               --  every right-hand-side.
               if not P_CC.Is_Empty then
                  declare
                     Ptr : Node_Id;
                  begin
                     Ptr := First (Component_Associations
                                     (P_CC.First_Element));
                     while Present (Ptr) loop
                        P_Expr.Append (Expression (Ptr));
                        Ptr := Next (Ptr);
                     end loop;
                  end;
               end if;
            end if;

         when E_Package =>
            if Refined then
               P_Expr := Node_Lists.Empty_List;
            else
               P_Expr := Find_Contracts (E, Name_Initial_Condition);
            end if;

         when others =>
            raise Program_Error;

      end case;

      return P_Expr;
   end Get_Postcondition_Expressions;

   ---------------------------
   -- Is_Precondition_Check --
   ---------------------------

   function Is_Precondition_Check (N : Node_Id) return Boolean
   is
      A : constant Node_Id := First (Pragma_Argument_Associations (N));
   begin
      pragma Assert (Nkind (Expression (A)) = N_Identifier);
      return Chars (Expression (A)) in Name_Pre | Name_Precondition;
   end Is_Precondition_Check;

   -----------------------------------
   -- Is_Initialized_At_Elaboration --
   -----------------------------------

   function Is_Initialized_At_Elaboration (F : Flow_Id;
                                           S : Flow_Scope)
                                           return Boolean
   is
   begin
      case F.Kind is
         when Direct_Mapping | Record_Field =>
            return Is_Initialized_At_Elaboration (Get_Direct_Mapping_Id (F),
                                                  S);

         when Magic_String | Synthetic_Null_Export =>
            return False;

         when Null_Value =>
            raise Program_Error;
      end case;
   end Is_Initialized_At_Elaboration;

end Flow_Utility;
