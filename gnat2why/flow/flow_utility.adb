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

with Ada.Containers.Hashed_Maps;

with Elists;                     use Elists;
with Errout;                     use Errout;
with Nlists;                     use Nlists;
with Output;                     use Output;
with Sprint;                     use Sprint;
with Treepr;                     use Treepr;

with Why;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Definition;           use SPARK_Definition;

with Flow_Debug;                 use Flow_Debug;
with Flow_Tree_Utility;          use Flow_Tree_Utility;

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
   --  Loop information
   ----------------------------------------------------------------------

   package Loop_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Flow_Id_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   Loop_Info_Frozen : Boolean       := False;
   Loop_Info        : Loop_Maps.Map := Loop_Maps.Empty_Map;

   ----------------------------------------------------------------------
   --  Local
   ----------------------------------------------------------------------

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
         Comp_F : constant Entity_Lists.Vector :=
           (if F.Kind = Record_Field
            then F.Component
            else Entity_Lists.Empty_Vector);

         Comp_RF : constant Entity_Lists.Vector :=
           (if The_Record_Field.Kind = Record_Field
            then The_Record_Field.Component
            else Entity_Lists.Empty_Vector);
      begin
         if Debug_Trace_Untangle then
            Write_Str ("Possibly include: ");
            Print_Flow_Id (F);
         end if;

         --  ??? Direct access into flow_id, should be removed somehow.
         if Comp_F.Length < Comp_RF.Length then
            return;
         end if;

         for I in Natural range 1 .. Natural (Comp_RF.Length) loop
            if Comp_RF (I) /= Comp_F (I) then
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
               Tmp.Append (Original_Record_Component (C));

               case Ekind (Get_Full_Type (C)) is
                  when Record_Kind =>
                     Process_Record (Get_Full_Type (C), Tmp);

                  when others =>
                     F := (Kind      => Record_Field,
                           Variant   => Normal_Use,
                           Node      => Entire_Var,
                           Bound     => Null_Bound,
                           Component => Tmp);
                     Possibly_Include (F);
               end case;
            end;

            C := Next_Component_Or_Discriminant (C);
         end loop;
      end Process_Record;

   begin
      if Debug_Trace_Untangle then
         Write_Str ("The_record_Field: ");
         Print_Flow_Id (The_Record_Field);
      end if;
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

            when Magic_String =>
               if not Is_Constant (F.Name) then
                  R.Include (F);
               end if;

            when Synthetic_Null_Export =>
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

   -------------------------------
   -- Has_User_Supplied_Globals --
   -------------------------------

   function Has_User_Supplied_Globals (Subprogram : Entity_Id)
                                       return Boolean
   is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Global)) or else
        Has_Depends (Subprogram);
   end Has_User_Supplied_Globals;

   -----------------
   -- Has_Depends --
   -----------------

   function Has_Depends (Subprogram : Entity_Id) return Boolean is
   begin
      return Present (Get_Pragma (Subprogram, Pragma_Depends));
   end Has_Depends;

   -----------------
   -- Get_Depends --
   -----------------

   procedure Get_Depends (Subprogram : Entity_Id;
                          Scope      : Flow_Scope;
                          Depends    : out Dependency_Maps.Map)
   is
      Tmp : Dependency_Maps.Map;
   begin

      ----------------------------------------------------------------------
      --  Step 1: parse the appropriate dependency relation.
      ----------------------------------------------------------------------

      Tmp := Parse_Depends (Get_Contract_Node (Subprogram,
                                               Scope,
                                               Depends_Contract));

      ----------------------------------------------------------------------
      --  Step 2: expand out any abstract state for which the refinement is
      --  visible, similar to what we do for globals.
      ----------------------------------------------------------------------

      Depends := Dependency_Maps.Empty_Map;
      for C in Tmp.Iterate loop
         declare
            D_In  : constant Flow_Id_Sets.Set :=
              (if Present (Dependency_Maps.Key (C))
               then To_Flow_Id_Set (Down_Project
                                      (Node_Sets.To_Set
                                         (Get_Direct_Mapping_Id
                                            (Dependency_Maps.Key (C))),
                                       Scope))
               else Flow_Id_Sets.To_Set (Dependency_Maps.Key (C)));

            D_Out : constant Flow_Id_Sets.Set :=
              To_Flow_Id_Set (Down_Project
                                (To_Node_Set (Dependency_Maps.Element (C)),
                                 Scope));
         begin
            for I of D_In loop
               Depends.Include (I, D_Out);
            end loop;
         end;
      end loop;

   end Get_Depends;

   -----------------
   -- Get_Globals --
   -----------------

   procedure Get_Globals (Subprogram             : Entity_Id;
                          Scope                  : Flow_Scope;
                          Proof_Ins              : out Flow_Id_Sets.Set;
                          Reads                  : out Flow_Id_Sets.Set;
                          Writes                 : out Flow_Id_Sets.Set;
                          Consider_Discriminants : Boolean := False;
                          Globals_For_Proof      : Boolean := False;
                          Use_Computed_Globals   : Boolean := True)
   is
      Global_Node  : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Global_Contract);
      Depends_Node : constant Node_Id := Get_Contract_Node (Subprogram,
                                                            Scope,
                                                            Depends_Contract);
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
            --  Add the given global to the reads, writes or proof_in
            --  list, depending on the mode.

            procedure Process (The_Mode   : Name_Id;
                               The_Global : Entity_Id)
            is
               Non_Limited_Global : constant Entity_Id :=
                 (if Ekind (The_Global) = E_Abstract_State
                    and then Present (Non_Limited_View (The_Global))
                  then Non_Limited_View (The_Global)
                  else The_Global);
               --  If a Non_Limited_View exists, then use that. In
               --  doing so we avoid generating two Flow_Ids for a
               --  single variable.
            begin
               case The_Mode is
                  when Name_Input =>
                     if not Globals_For_Proof or else
                       Ekind (Non_Limited_Global) /= E_In_Parameter
                     then
                        --  Proof does not count in parameters as
                        --  globals (as they are constants).
                        G_In.Insert (Non_Limited_Global);
                     end if;

                  when Name_In_Out =>
                     G_In.Insert (Non_Limited_Global);
                     G_Out.Insert (Non_Limited_Global);

                  when Name_Output =>
                     if Consider_Discriminants and then
                       Contains_Discriminants
                       (Direct_Mapping_Id (Non_Limited_Global, In_View))
                     then
                        G_In.Insert (Non_Limited_Global);
                     end if;
                     G_Out.Insert (Non_Limited_Global);

                  when Name_Proof_In =>
                     if not Globals_For_Proof or else
                       Ekind (Non_Limited_Global) /= E_In_Parameter
                     then
                        --  See above.
                        G_Proof.Insert (Non_Limited_Global);
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

            if Debug_Trace_Get_Global then
               Indent;
               Write_Str ("proof ins");
               Write_Eol;
               Indent;
               for F of Proof_Ins loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("reads");
               Write_Eol;
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("writes");
               Write_Eol;
               Indent;
               for F of Writes loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;
               Outdent;
            end if;

         end;

      elsif Present (Depends_Node) then

         --  If we have no global, but we do have a depends, we can
         --  reverse-engineer the global. This also solves the issue where
         --  the (computed) global is inconsistent with the depends. (See
         --  M807-032 for an example.)

         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("reversing depends annotation");
            Write_Eol;
            Outdent;
         end if;

         declare
            D_Map  : Dependency_Maps.Map;
            Params : Node_Sets.Set;
            E      : Entity_Id;
         begin
            Get_Depends (Subprogram => Subprogram,
                         Scope      => Scope,
                         Depends    => D_Map);

            --  We need to make sure not to include our own parameters in
            --  the globals we produce here.

            E := First_Formal (Subprogram);
            while Present (E) loop
               Params.Include (E);
               E := Next_Formal (E);
            end loop;

            --  Always OK to call direct_mapping here since you can't refer
            --  to hidden state in user-written depends contracts.

            for C in D_Map.Iterate loop
               declare
                  Output : constant Flow_Id := Dependency_Maps.Key (C);
                  Inputs : constant Flow_Id_Sets.Set :=
                    Dependency_Maps.Element (C);
               begin
                  E := (if Present (Output)
                        then Get_Direct_Mapping_Id (Output)
                        else Empty);
                  if Present (E) and then E /= Subprogram
                    and then not Params.Contains (E)
                  then
                     --  Note we also filter out the function'result
                     --  construct here.
                     Writes.Include (Change_Variant (Output, Out_View));
                  end if;

                  for R of Inputs loop
                     E := (if Present (R)
                           then Get_Direct_Mapping_Id (R)
                           else Empty);
                     if Present (E) and then not Params.Contains (E) then
                        Reads.Include (Change_Variant (R, In_View));

                        if Has_Effective_Reads (R) then
                           --  A volatile with effective reads is always an
                           --  output as well (this should be recorded in
                           --  the depends, but the front-end does not
                           --  enforce this).
                           Writes.Include (Change_Variant (R, Out_View));
                        end if;
                     end if;
                  end loop;
               end;
            end loop;

            if Debug_Trace_Get_Global then
               Indent;
               Write_Str ("reads");
               Write_Eol;
               Indent;
               for F of Reads loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;

               Write_Str ("writes");
               Write_Eol;
               Indent;
               for F of Writes loop
                  Sprint_Flow_Id (F);
                  Write_Eol;
               end loop;
               Outdent;
               Outdent;
            end if;
         end;

      elsif Use_Computed_Globals then
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
               E : constant Entity_Id := Find_Entity (Name);
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

      else
         --  We don't have user globals and we're not allowed to use
         --  computed globals (i.e. we're trying to compute globals).

         if Debug_Trace_Get_Global then
            Indent;
            Write_Str ("defaulting to null globals");
            Write_Eol;
            Outdent;
         end if;

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
                        --  We simply ignore the null refinement, it is
                        --  treated as if it was not present.
                        if Nkind (Node (Ptr)) /= N_Null then
                           Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                                 F.Variant)));
                        end if;
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     Ptr := First_Elmt (Part_Of_Constituents
                                          (Get_Direct_Mapping_Id (F)));
                     while Present (Ptr) loop
                        --  Part_of cannot include a null refinement.
                        Tmp.Union (Expand (Direct_Mapping_Id (Node (Ptr),
                                                              F.Variant)));
                        Ptr := Next_Elmt (Ptr);
                     end loop;

                     if Tmp.Is_Empty then
                        --  If we can't refine this state (maybe the body
                        --  is not in SPARK, or simply not implemented or
                        --  there is a null refinement) then we use the
                        --  abstract state itself.
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

   ----------------------
   -- Get_Function_Set --
   ----------------------

   function Get_Function_Set (N : Node_Id) return Node_Sets.Set is
      NS : Node_Sets.Set := Node_Sets.Empty_Set;

      function Proc (N : Node_Id) return Traverse_Result;
      --  If the node being processed is an N_Function call, it add
      --  the corresponding Flow_Id to FS.

      ----------
      -- Proc --
      ----------

      function Proc (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) = N_Function_Call then
            NS.Include (Entity (Name (N)));
         end if;

         return OK;
      end Proc;

      procedure Traverse is new Traverse_Proc (Process => Proc);

   begin
      Traverse (N);
      return NS;
   end Get_Function_Set;

   ----------------------
   -- Get_Variable_Set --
   ----------------------

   function Get_Variable_Set
     (N                            : Node_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
      Reduced                      : Boolean := False;
      Allow_Statements             : Boolean := False;
      Expand_Synthesized_Constants : Boolean := False)
      return Flow_Id_Sets.Set
   is
      VS : Flow_Id_Sets.Set;

      function Recurse_On (N : Node_Id) return Flow_Id_Sets.Set
      is (Get_Variable_Set
            (N,
             Scope                        => Scope,
             Local_Constants              => Local_Constants,
             Fold_Functions               => Fold_Functions,
             Use_Computed_Globals         => Use_Computed_Globals,
             Reduced                      => Reduced,
             Allow_Statements             => False,
             Expand_Synthesized_Constants => Expand_Synthesized_Constants));
      --  Recuse on N. Please note that Allow_Statements is always false;
      --  this is intentional as we should only ever recurse on something
      --  inside expressions.

      function Process_Subprogram_Call
        (Callsite : Node_Id)
         return Flow_Id_Sets.Set
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

      function Process_Subprogram_Call
        (Callsite : Node_Id)
         return Flow_Id_Sets.Set
      is
         Subprogram    : constant Entity_Id := Entity (Name (Callsite));

         Global_Reads  : Flow_Id_Sets.Set;
         Global_Writes : Flow_Id_Sets.Set;

         Folding       : constant Boolean :=
           Fold_Functions
           and then Ekind (Subprogram) = E_Function
           and then Has_Depends (Subprogram);

         Used_Reads    : Flow_Id_Sets.Set;

         V             : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin

         --  Determine the global effects of the called program.

         declare
            Proof_Reads : Flow_Id_Sets.Set;
         begin
            Get_Globals (Subprogram           => Subprogram,
                         Scope                => Scope,
                         Proof_Ins            => Proof_Reads,
                         Reads                => Global_Reads,
                         Writes               => Global_Writes,
                         Use_Computed_Globals => Use_Computed_Globals);
            if not Fold_Functions then
               Global_Reads.Union (Proof_Reads);
            end if;
         end;

         --  If we fold functions we need to obtain the used inputs.

         if Folding then
            declare
               Depends : Dependency_Maps.Map;
            begin
               Get_Depends (Subprogram => Subprogram,
                            Scope      => Scope,
                            Depends    => Depends);
               pragma Assert (Depends.Length in 1 .. 2);
               Used_Reads := Depends (Direct_Mapping_Id (Subprogram));
            end;
         end if;

         --  Apply sanity check for functions.

         if Nkind (Callsite) = N_Function_Call and then
           Flow_Id_Sets.Length (Global_Writes) > 0
         then
            Error_Msg_NE
              (Msg =>
                 "side-effects of function & are not modelled in SPARK",
               N   => Callsite,
               E   => Subprogram);
         end if;

         --  Merge globals into the variables used.

         for G of Global_Reads loop
            if (if Folding
                then Used_Reads.Contains (Change_Variant (G, Normal_Use)))
            then
               V.Include (Change_Variant (G, Normal_Use));
            end if;
         end loop;
         for G of Global_Writes loop
            V.Include (Change_Variant (G, Normal_Use));
         end loop;

         --  Merge the actuals into the set of variables used.

         declare
            Actual : Node_Id;
            Formal : Entity_Id;
            Call   : Node_Id;
            Ptr    : Node_Id;
         begin
            Ptr := First (Parameter_Associations (Callsite));
            while Present (Ptr) loop
               case Nkind (Ptr) is
                  when N_Parameter_Association =>
                     Actual := Explicit_Actual_Parameter (Ptr);
                  when others =>
                     Actual := Ptr;
               end case;

               Find_Actual (N      => Actual,
                            Formal => Formal,
                            Call   => Call);
               pragma Assert (Call = Callsite);

               if (if Folding
                   then Used_Reads.Contains (Direct_Mapping_Id (Formal)))
               then
                  V.Union (Recurse_On (Actual));
               end if;

               Next (Ptr);
            end loop;
         end;

         --  Finally, we expand the collected set (if necessary).

         return R : Flow_Id_Sets.Set do
            R := Flow_Id_Sets.Empty_Set;
            for Tmp of V loop
               if Reduced or Tmp.Kind = Record_Field then
                  R.Include (Tmp);
               else
                  R.Union (Flatten_Variable (Tmp));
               end if;
            end loop;
         end return;
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
                  VS.Union (Process_Subprogram_Call (N));
                  return Skip;
               end if;

            when N_Later_Decl_Item =>
               --  These should allow us to go through package specs
               --  and bodies.
               return Skip;

            when N_Function_Call =>
               VS.Union (Process_Subprogram_Call (N));
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
                              VS.Union (Recurse_On (E));
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

            when N_Aggregate =>
               VS.Union (Recurse_On (Aggregate_Bounds (N)));

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
                     A, B, C, D : Flow_Id_Sets.Set;
                  begin
                     Untangle_Assignment_Target
                       (N                    => N,
                        Scope                => Scope,
                        Local_Constants      => Local_Constants,
                        Use_Computed_Globals => Use_Computed_Globals,
                        Vars_Explicitly_Used => A,
                        Vars_Implicitly_Used => B,
                        Vars_Defined         => C,
                        Vars_Semi_Used       => D);
                     VS.Union (A);
                     VS.Union (B);
                     VS.Union (C);
                     if not Fold_Functions then
                        VS.Union (D);
                     end if;
                  end;
                  return Skip;

               else

                  return Skip;

               end if;

            when N_Attribute_Reference =>
               case Get_Attribute_Id (Attribute_Name (N)) is
                  when Attribute_Constrained =>
                     declare
                        A, B, C, D : Flow_Id_Sets.Set;
                     begin
                        Untangle_Assignment_Target
                          (N                    => Prefix (N),
                           Scope                => Scope,
                           Local_Constants      => Local_Constants,
                           Use_Computed_Globals => Use_Computed_Globals,
                           Vars_Explicitly_Used => A,
                           Vars_Implicitly_Used => B,
                           Vars_Defined         => C,
                           Vars_Semi_Used       => D);
                        VS.Union (A);
                        if not Fold_Functions then
                           VS.Union (D);
                        end if;
                     end;
                     return Skip;

                  when Attribute_First |
                    Attribute_Last     |
                    Attribute_Length   |
                    Attribute_Range    =>
                     for F of Recurse_On (Prefix (N)) loop
                        if F.Kind in Direct_Mapping | Record_Field and then
                          F.Bound.Kind = No_Bound and then
                          Has_Bounds (F)
                        then
                           --  This is not a bound variable, but it
                           --  requires bounds tracking. We make it a
                           --  bound variable.
                           VS.Include
                             (F'Update (Bound => (Kind => Some_Bound)));

                        else
                           --  This is something else. We just copy it.
                           VS.Include (F);
                        end if;
                     end loop;
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

   begin --  Get_Variable_Set
      Traverse (N);
      return Filter_Out_Non_Local_Constants (VS, Local_Constants);
   end Get_Variable_Set;

   function Get_Variable_Set
     (L                            : List_Id;
      Scope                        : Flow_Scope;
      Local_Constants              : Node_Sets.Set;
      Fold_Functions               : Boolean;
      Use_Computed_Globals         : Boolean;
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
               Fold_Functions               => Fold_Functions,
               Use_Computed_Globals         => Use_Computed_Globals,
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
      Use_Computed_Globals : Boolean;
      Vars_Defined         : in out Flow_Id_Sets.Set;
      Vars_Explicitly_Used : in out Flow_Id_Sets.Set;
      Vars_Implicitly_Used : in out Flow_Id_Sets.Set;
      Vars_Semi_Used       : in out Flow_Id_Sets.Set)
   is
      --  Fold_Functions (a parameter for Get_Variable_Set) is specified as
      --  `false' here because Untangle should only ever be called where we
      --  assign something to something. And you can't assign to function
      --  results (yet).

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
         Used_All    : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
         Used_Folded : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
      begin
         case Nkind (N) is
            when N_Indexed_Component | N_Attribute_Reference =>
               Used_All := Get_Variable_Set
                 (Expressions (N),
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => False,
                  Use_Computed_Globals => Use_Computed_Globals);
               Used_Folded := Get_Variable_Set
                 (Expressions (N),
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => Use_Computed_Globals);
            when N_Slice =>
               Used_All := Get_Variable_Set
                 (Discrete_Range (N),
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => False,
                  Use_Computed_Globals => Use_Computed_Globals);
               Used_Folded := Get_Variable_Set
                 (Discrete_Range (N),
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => True,
                  Use_Computed_Globals => Use_Computed_Globals);
            when others =>
               return OK;
         end case;

         Vars_Explicitly_Used.Union (Used_Folded);
         Vars_Semi_Used.Union (Used_All - Used_Folded);
         return OK;
      end Proc;

      procedure Merge_Array_Expressions is new Traverse_Proc (Proc);

      Bottom_Node   : Node_Id;
      End_Of_Record : Node_Id;
      Partial_Use   : Boolean;

   begin
      if Debug_Trace_Untangle then
         Sprint_Node (N);
         Print_Node_Subtree (N);
      end if;

      case Nkind (N) is
         when N_Type_Conversion | N_Unchecked_Type_Conversion =>
            Untangle_Assignment_Target
              (N                    => Expression (N),
               Scope                => Scope,
               Local_Constants      => Local_Constants,
               Use_Computed_Globals => Use_Computed_Globals,
               Vars_Defined         => Vars_Defined,
               Vars_Explicitly_Used => Vars_Explicitly_Used,
               Vars_Implicitly_Used => Vars_Implicitly_Used,
               Vars_Semi_Used       => Vars_Semi_Used);

         when N_Identifier | N_Expanded_Name =>
            --  X :=
            Vars_Defined.Union
              (Get_Variable_Set
                 (N,
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => False,
                  Use_Computed_Globals => Use_Computed_Globals));

         when N_Function_Call =>
            --  Not strictly right, but this will satisfy the
            --  postcondition.
            Vars_Defined.Union
              (Get_Variable_Set
                 (N,
                  Scope                => Scope,
                  Local_Constants      => Local_Constants,
                  Fold_Functions       => False,
                  Use_Computed_Globals => Use_Computed_Globals));

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
            if Debug_Trace_Untangle then
               Write_Str ("Bottom_Node: ");
               Print_Node_Briefly (Bottom_Node);
               Write_Str ("End_Of_Record: ");
               Print_Node_Briefly (End_Of_Record);
            end if;

            case Nkind (Bottom_Node) is
               when N_Identifier | N_Expanded_Name =>
                  null;

               when N_Attribute_Reference =>
                  null;

               when others =>
                  Vars_Explicitly_Used.Union
                    (Get_Variable_Set
                       (Bottom_Node,
                        Scope                => Scope,
                        Local_Constants      => Local_Constants,
                        Fold_Functions       => False,
                        Use_Computed_Globals => Use_Computed_Globals));
                  goto Fin;
            end case;

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
                              Scope                => Scope,
                              Local_Constants      => Local_Constants,
                              Fold_Functions       => False,
                              Use_Computed_Globals => Use_Computed_Globals));

                     when N_Unchecked_Type_Conversion =>
                        --  This is an interesting special case. We
                        --  are querying a specific record field of
                        --  the result of an unchecked conversion. The
                        --  variables used and defined should be the
                        --  argument to the unchecked conversion.
                        Vars_Defined.Union
                          (Get_Variable_Set
                             (Expression (Prefix (End_Of_Record)),
                              Scope                => Scope,
                              Local_Constants      => Local_Constants,
                              Fold_Functions       => False,
                              Use_Computed_Globals => Use_Computed_Globals));

                        --  Since we are using the defined variable
                        --  only partially, we need to make sure its
                        --  also used.
                        Vars_Implicitly_Used.Union (Vars_Defined);

                     when N_Attribute_Reference =>
                        if Attribute_Name (Prefix (End_Of_Record)) =
                          Name_Update
                        then
                           --  Here, we are adding all variables
                           --  used within the 'Update attribute.
                           Vars_Defined.Union
                             (Get_Variable_Set
                                (Expressions (Prefix (End_Of_Record)),
                                 Scope                => Scope,
                                 Local_Constants      => Local_Constants,
                                 Fold_Functions       => False,
                                 Use_Computed_Globals =>
                                   Use_Computed_Globals));
                        end if;

                        --  We also add the record field itself. If we
                        --  are dealing with a record instead of a
                        --  record field, then we add all record
                        --  components.
                        Vars_Defined.Union
                          (All_Record_Components
                             (Record_Field_Id (End_Of_Record)));

                        Vars_Implicitly_Used.Union (Vars_Defined);

                     when others =>
                        declare
                           F : constant Flow_Id :=
                             Record_Field_Id (End_Of_Record);
                           S : constant Flow_Id_Sets.Set :=
                             All_Record_Components
                             (Record_Field_Id (End_Of_Record));
                        begin
                           if Debug_Trace_Untangle then
                              Write_Str ("Field to split: ");
                              Print_Flow_Id (F);
                              Write_Str ("To merge: ");
                              Print_Node_Set (S);
                           end if;

                           Vars_Defined.Union (S);
                           if Partial_Use then
                              Vars_Implicitly_Used.Union (S);
                           end if;
                        end;
                  end case;

               when N_Indexed_Component | N_Slice =>
                  raise Program_Error;

               when N_Function_Call =>
                  --  Not strictly right, but this will satisfy the
                  --  postcondition.
                  Vars_Defined.Union
                    (Get_Variable_Set
                       (End_Of_Record,
                        Scope                => Scope,
                        Local_Constants      => Local_Constants,
                        Fold_Functions       => False,
                        Use_Computed_Globals => Use_Computed_Globals));

               when N_Unchecked_Type_Conversion =>
                  --  See above.
                  Vars_Defined.Union
                    (Get_Variable_Set
                       (Expression (End_Of_Record),
                        Scope           => Scope,
                        Local_Constants => Local_Constants,
                        Fold_Functions  => False,
                        Use_Computed_Globals => Use_Computed_Globals));

               when N_Attribute_Reference =>

                  if Present (Expressions (End_Of_Record)) then
                     Vars_Explicitly_Used.Union
                       (Get_Variable_Set
                          (Expressions (End_Of_Record),
                           Scope                => Scope,
                           Local_Constants      => Local_Constants,
                           Fold_Functions       => False,
                           Use_Computed_Globals => Use_Computed_Globals));
                  end if;

                  Untangle_Assignment_Target
                    (N                    => Prefix (End_Of_Record),
                     Scope                => Scope,
                     Local_Constants      => Local_Constants,
                     Use_Computed_Globals => Use_Computed_Globals,
                     Vars_Defined         => Vars_Defined,
                     Vars_Explicitly_Used => Vars_Explicitly_Used,
                     Vars_Implicitly_Used => Vars_Implicitly_Used,
                     Vars_Semi_Used       => Vars_Semi_Used);

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

   <<Fin>>
      if Debug_Trace_Untangle then
         Print_Node_Set (Vars_Explicitly_Used);
         Print_Node_Set (Vars_Implicitly_Used);
         Print_Node_Set (Vars_Defined);
      end if;
   end Untangle_Assignment_Target;

   ----------------------------------
   -- Get_Precondition_Expressions --
   ----------------------------------

   function Get_Precondition_Expressions (E : Entity_Id) return Node_Lists.List
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

   -------------------------------------
   -- Is_Initialized_In_Specification --
   -------------------------------------

   function Is_Initialized_In_Specification (F : Flow_Id;
                                             S : Flow_Scope)
                                             return Boolean
   is
      pragma Assert (F.Kind in Direct_Mapping | Record_Field);
      E : constant Entity_Id := Get_Direct_Mapping_Id (F);
   begin
      case Ekind (E) is
         when E_Abstract_State =>
            return False;

         when others =>
            pragma Assert (Nkind (Parent (E)) = N_Object_Declaration);
            return Present (Expression (Parent (E)));

      end case;
   end Is_Initialized_In_Specification;

   --------------
   -- Add_Loop --
   --------------

   procedure Add_Loop (E : Entity_Id)
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info.Insert (E, Flow_Id_Sets.Empty_Set);
   end Add_Loop;

   --------------------
   -- Add_Loop_Write --
   --------------------

   procedure Add_Loop_Write (E : Entity_Id;
                             F : Flow_Id)
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      pragma Assert (Loop_Info.Contains (E));
      Loop_Info (E).Include (F);
   end Add_Loop_Write;

   ----------------------
   -- Freeze_Loop_Info --
   ----------------------

   procedure Freeze_Loop_Info
   is
   begin
      pragma Assert (not Loop_Info_Frozen);
      Loop_Info_Frozen := True;
   end Freeze_Loop_Info;

   -----------------------
   -- Loop_Writes_Known --
   -----------------------

   function Loop_Writes_Known (E : Entity_Id) return Boolean
   is
   begin
      return Loop_Info_Frozen and then Loop_Info.Contains (E);
   end Loop_Writes_Known;

   ---------------------
   -- Get_Loop_Writes --
   ---------------------

   function Get_Loop_Writes (E : Entity_Id) return Flow_Id_Sets.Set
   is
   begin
      return Loop_Info (E);
   end Get_Loop_Writes;

end Flow_Utility;
