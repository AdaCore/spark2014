------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2017, AdaCore                  --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings;                use Ada.Strings;
with Ada.Strings.Fixed;          use Ada.Strings.Fixed;
with Exp_Util;                   use Exp_Util;
with Flow_Types;
with Flow_Utility;
with Gnat2Why.Annotate;
with Gnat2Why_Args;
with Gnat2Why.Expr;              use Gnat2Why.Expr;
with Lib;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with Sem_Aux;                    use Sem_Aux;
with Sem_Util;                   use Sem_Util;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util.External_Axioms; use SPARK_Util.External_Axioms;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;
with String_Utils;               use String_Utils;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Inter;                  use Why.Inter;
with Why.Types;                  use Why.Types;

package body Gnat2Why.Util is

   Why3_Keywords : String_Utils.String_Sets.Set;

   procedure Make_Empty_Why_Section
     (Kind : W_Section_Id; Section : out Why_Section)
     with Post => (Section.Cur_Theory = Why.Types.Why_Empty);
   --  Return an empty Why_Section with the given kind

   function Check_DIC_At_Declaration (E : Entity_Id) return Boolean with
     Pre => Present (Get_Initial_DIC_Procedure (E));
   --  @param Ty type entity with a DIC (inherited or not)
   --  @return True if the DIC expression depends on the current type instance.
   --        If it depends on the type instance, it is considered as a
   --        postcondtion of the default initialization of the private type,
   --        and is checked at declaration. If it does not depend on the type
   --        instance, it is considered as a precondition of the default
   --        initialization, and is checked at use.

   --------------------
   -- Ada_Ent_To_Why --
   --------------------

   package body Ada_Ent_To_Why is

      function Normalize_Entity (E : Entity_Id) return Entity_Id is
        (if Nkind (E) in N_Entity and then Ekind (E) = E_Discriminant then
              Root_Record_Component (E) else E);
      --  Entities of discriminants can vary when types are derived. We want to
      --  refer to the same item for every variants of a single discriminant
      --  entity.
      --  ??? Ada_Ent_To_Why is sometimes used to store nodes, see
      --      Transform_Aggregate.
      --  @param E entity to be registered in the map
      --  @return a normalized version of E to avoid duplicates

      -------------
      -- Element --
      -------------

      function Element (M : Map; E : Entity_Id) return Item_Type is
         Uniq_Ent : constant Entity_Id := Normalize_Entity (E);
      begin
         return M.Entity_Ids.Element (Uniq_Ent);
      end Element;

      function Element (C : Cursor) return Item_Type is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ent_To_Why.Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Element (C.Name_Cursor);
         end case;
      end Element;

      ----------
      -- Find --
      ----------

      function Find (M : Map; E : Entity_Id) return Cursor is
         Uniq_Ent : constant Entity_Id := Normalize_Entity (E);
         C        : constant Ent_To_Why.Cursor := M.Entity_Ids.Find (Uniq_Ent);
      begin
         if Ent_To_Why.Has_Element (C) then
            return Cursor'(CK_Ent,
                           C,
                           Name_To_Why_Map.No_Element);
         else
            return Cursor'(CK_Ent, Ent_To_Why.No_Element,
                           Name_To_Why_Map.No_Element);
         end if;
      end Find;

      function Find (M : Map; E : Entity_Name) return Cursor is
         C : constant Name_To_Why_Map.Cursor := M.Entity_Names.Find (E);
      begin
         if Name_To_Why_Map.Has_Element (C) then
            return Cursor'(CK_Str, Ent_To_Why.No_Element,
                           C);
         else
            declare
               Ent      : constant Entity_Id := Find_Entity (E);
               Uniq_Ent : constant Entity_Id := Normalize_Entity (Ent);
            begin
               if Present (Uniq_Ent) then
                  return Find (M, Uniq_Ent);
               else
                  return Cursor'(CK_Ent, Ent_To_Why.No_Element,
                                 Name_To_Why_Map.No_Element);
               end if;
            end;
         end if;
      end Find;

      -----------------
      -- Has_Element --
      -----------------

      function Has_Element (M : Map; E : Entity_Id) return Boolean is
         Uniq_Ent : constant Entity_Id := Normalize_Entity (E);
      begin
         return M.Entity_Ids.Contains (Uniq_Ent);
      end Has_Element;

      function Has_Element (C : Cursor) return Boolean
      is
      begin
         case C.Kind is
            when CK_Ent =>
               return Ent_To_Why.Has_Element (C.Ent_Cursor);
            when CK_Str =>
               return Name_To_Why_Map.Has_Element (C.Name_Cursor);
         end case;
      end Has_Element;

      ------------
      -- Insert --
      ------------

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Item_Type)
      is
         Uniq_Ent : constant Entity_Id := Normalize_Entity (E);
         C        : Ent_To_Why.Cursor;
         Inserted : Boolean;
      begin
         M.Entity_Ids.Insert (Uniq_Ent, W, C, Inserted);
         if Undo_Stacks.Is_Empty (M.Undo_Stack) then

            --  At the global level (no undo stack) we expect that there are no
            --  clashes in symbols.

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Ent, Uniq_Ent));
            else

               --  If there was already an entry for the entity, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted

               M.Undo_Stack.Append
                 (Action'(Kind       => Insert_Ent,
                          Ins_Entity => Ent_To_Why.Key (C),
                          Ins_Binder => Ent_To_Why.Element (C)));
               M.Entity_Ids.Replace (Uniq_Ent, W);
               M.Undo_Stack.Append (Action'(Remove_Ent, Uniq_Ent));
            end if;
         end if;
      end Insert;

      procedure Insert (M : in out Map;
                        E : Entity_Name;
                        W : Item_Type) is
         C : Name_To_Why_Map.Cursor;
         Inserted : Boolean;
      begin
         M.Entity_Names.Insert (E, W, C, Inserted);
         if Undo_Stacks.Is_Empty (M.Undo_Stack) then

            --  At the global level (no undo stack) we expect that there are no
            --  clashes in symbols

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Name, E));
            else

               --  If there was already an entry for the name, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted.

               M.Undo_Stack.Append
                 (Action'(Kind => Insert_Name,
                          Ins_Name => Name_To_Why_Map.Key (C),
                          Ins_Binder => Name_To_Why_Map.Element (C)));
               M.Entity_Names.Replace (E, W);
               M.Undo_Stack.Append (Action'(Remove_Name, E));
            end if;
         end if;
      end Insert;

      ---------------
      -- Pop_Scope --
      ---------------

      procedure Pop_Scope (M : in out Map) is

         procedure Apply_Action (C : Undo_Stacks.Cursor);
         --  apply a single action

         ------------------
         -- Apply_Action --
         ------------------

         procedure Apply_Action (C : Undo_Stacks.Cursor) is
            A : constant Action := Undo_Stacks.Element (C);
         begin
            case A.Kind is
               when Insert_Ent =>
                  M.Entity_Ids.Include (A.Ins_Entity, A.Ins_Binder);
               when Insert_Name =>
                  M.Entity_Names.Include (A.Ins_Name, A.Ins_Binder);
               when Remove_Ent =>
                  M.Entity_Ids.Delete (A.Rem_Entity);
               when Remove_Name =>
                  M.Entity_Names.Delete (A.Rem_Name);
               when Boundary =>
                  raise Program_Error;
            end case;
         end Apply_Action;

         C : Undo_Stacks.Cursor := M.Undo_Stack.Last;
         Tmp : Undo_Stacks.Cursor;

      --  Start of processing for Pop_Scope

      begin
         while Undo_Stacks.Has_Element (C) and then
           Undo_Stacks.Element (C).Kind /= Boundary loop
            Apply_Action (C);
            Tmp := C;
            Undo_Stacks.Previous (C);
            M.Undo_Stack.Delete (Tmp);
         end loop;

         --  we still need to delete the boundary marker, if it exists

         if Undo_Stacks.Has_Element (C) then
            M.Undo_Stack.Delete (C);
         end if;
      end Pop_Scope;

      ----------------
      -- Push_Scope --
      ----------------

      procedure Push_Scope (M : in out Map) is
      begin
         M.Undo_Stack.Append (Action'(Kind => Boundary));
      end Push_Scope;

   end Ada_Ent_To_Why;

   -------------------------------
   -- Get_Counterexample_Labels --
   -------------------------------

   function Get_Counterexample_Labels
     (E              : Entity_Id;
      Append_To_Name : String := "") return Name_Id_Sets.Set
   is
      Labels : Name_Id_Sets.Set;
      Model_Trace : constant Name_Id_Sets.Set := Get_Model_Trace_Label
        (E, False, Append_To_Name);

      E_Type : constant Entity_Id := Retysp (Etype (E));
      --  Taking the full_view of the type to be able to match private
      --  type in the same way as other types because the current intended
      --  behavior is to print private types as if they were public.

   begin
      if not Comes_From_Source (E)
            and then not Comes_From_Source (Parent (E))
      then
         Labels := Name_Id_Sets.Empty_Set;

      --  Generate counterexample labels for a function result. As function
      --  results are translated as refs, we must generate a "model_projected"
      --  label.

      elsif Ekind (E) = E_Function then
         Labels := Model_Trace;
         Labels.Include (Model_Projected);

      --  Generate counterexample labels for variables of supported types.
      --  For every supported type, we must be decide whether generate "model"
      --  or "model_projected" label. If Why3 builtin type is used for E, the
      --  label "model" can be generated, in other cases the label
      --  "model_projected" must be generated.
      --
      --  Note that the label "model_projected" can be generated in all cases,
      --  but it introduces extra overhead in the number of logical variables
      --  in the generated formula.

      else
         case Ekind (E_Type) is
            when Scalar_Kind =>
               Labels := Model_Trace;

               --  If the type used in Why3 for the entity is not abstract or
               --  the entity is not mutable, the type is builtin Why3 type.

               if Get_Type_Kind (Type_Of_Node (Etype (E))) /= EW_Abstract
                 and then not Is_Mutable_In_Why (E)
               then
                  --  Request directly the value of E in the counterexample.

                  Labels.Include (Model);
               else
                  --  Ask the value of E projected to Why3 builtin type in the
                  --  counterexample.
                  --
                  --  If E is of an abstract type, the value of E is projected
                  --  to the corresponding concrete type using a projection
                  --  function. If E is mutable, it is translated as a ref
                  --  (a record with one mutable field representing the value
                  --  of E) in Why3 in Translate_Variable. The value of E is
                  --  projected to this field (and then further if it is still
                  --  not of Why3 Builting type).

                  Labels.Include (Model_Projected);
               end if;

            when Record_Kind
               | Array_Kind
            =>
               Labels := Model_Trace;
               Labels.Include (Model_Projected);

         when others =>
            null;
         end case;
      end if;

      return Labels;
   end Get_Counterexample_Labels;

   ------------------
   -- Add_To_Graph --
   ------------------

   procedure Add_To_Graph (Map : in out Node_Graphs.Map; From, To : Node_Id) is
      Position : Node_Graphs.Cursor;
      Ignored  : Boolean;

   begin
      --  Insert an empty set or do nothing
      Map.Insert (Key => From, Position => Position, Inserted => Ignored);
      Map (Position).Include (To);
   end Add_To_Graph;

   ------------------------
   -- Avoid_Why3_Keyword --
   ------------------------

   function Avoid_Why3_Keyword (S : String) return String is
      S_Copy : String := S;
   begin
      Lower_Case_First (S_Copy);
      if Why3_Keywords.Contains (S_Copy) then
         return S_Copy & "__";
      else
         return S_Copy;
      end if;
   end Avoid_Why3_Keyword;

   -------------------------
   -- BitVector_Type_Size --
   -------------------------

   function BitVector_Type_Size (Typ : W_Type_Id) return Uint is
   begin
      return (if Typ = EW_BitVector_8_Type then Uint_8
              elsif Typ = EW_BitVector_16_Type then Uint_16
              elsif Typ = EW_BitVector_32_Type then Uint_32
              elsif Typ = EW_BitVector_64_Type then Uint_64
              else raise Program_Error);
   end BitVector_Type_Size;

   ------------------------------
   -- Check_DIC_At_Declaration --
   ------------------------------

   function Check_DIC_At_Declaration (E : Entity_Id) return Boolean is
      Ty                : constant Entity_Id := Retysp (E);
      Default_Init_Subp : constant Entity_Id := Get_Initial_DIC_Procedure (E);
      Default_Init_Expr : constant Node_Id :=
        Get_Expr_From_Check_Only_Proc (Default_Init_Subp);
      Init_Param        : constant Entity_Id :=
        Defining_Entity (First (Parameter_Specifications
                          (Subprogram_Specification (Default_Init_Subp))));
   begin
      return Present (Default_Init_Expr)
        and then Flow_Utility.Get_Variables_For_Proof (Default_Init_Expr, Ty)
         .Contains (Flow_Types.Direct_Mapping_Id (Unique_Entity (Init_Param)));
   end Check_DIC_At_Declaration;

   ------------------
   -- Compute_Spec --
   ------------------

   function Compute_Spec
     (Params : Transformation_Params;
      Nodes  : Node_Lists.List;
      Domain : EW_Domain) return W_Expr_Id
   is
      Cur_Spec : W_Expr_Id;
   begin
      if Nodes.Is_Empty then
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;

      Cur_Spec := Why_Empty;

      for Node of Nodes loop
         declare
            Why_Expr : constant W_Expr_Id :=
              Transform_Expr (Node, EW_Bool_Type, Domain, Params);
         begin
            if Cur_Spec /= Why_Empty then
               Cur_Spec :=
                 New_And_Then_Expr
                   (Left   => Why_Expr,
                    Right  => Cur_Spec,
                    Domain => Domain);
            else
               Cur_Spec := Why_Expr;
            end if;
         end;
      end loop;

      return Cur_Spec;
   end Compute_Spec;

   function Compute_Spec
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Kind      : Pragma_Id;
      Domain    : EW_Domain;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return W_Expr_Id
   is
      Nodes : constant Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide, Inherited);
   begin
      return Compute_Spec (Params, Nodes, Domain);
   end Compute_Spec;

   -------------------------
   -- Count_Discriminants --
   -------------------------

   function Count_Discriminants (E : Entity_Id) return Natural is
   begin
      if not Has_Discriminants (E)
        and then not Has_Unknown_Discriminants (E)
      then
         return 0;
      end if;

      declare
         Discr : Entity_Id := First_Discriminant (E);
         Count : Natural := 0;
      begin
         while Present (Discr) loop
            if Is_Not_Hidden_Discriminant (Discr) then
               Count := Count + 1;
            end if;
            Next_Discriminant (Discr);
         end loop;
         return Count;
      end;
   end Count_Discriminants;

   ------------------------------
   -- Count_Why_Regular_Fields --
   ------------------------------

   function Count_Why_Regular_Fields (E : Entity_Id) return Natural is
      Count : Natural := Natural (Get_Component_Set (E).Length);

   begin
      --  Add one field for tagged types to represent the unknown extension
      --  components. The field for the tag itself is stored directly in the
      --  Why3 record.

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Regular_Fields;

   --------------------------------
   -- Count_Why_Top_Level_Fields --
   --------------------------------

   function Count_Why_Top_Level_Fields (E : Entity_Id) return Natural is
      Count : Natural := 0;

   begin
      --  Store discriminants in a separate sub-record field, so that
      --  subprograms that cannot modify discriminants are passed this
      --  sub-record by copy instead of by reference (with the split version
      --  of the record).

      if Count_Discriminants (E) > 0 then
         Count := Count + 1;
      end if;

      --  Store components in a separate sub-record field. This includes:
      --    . visible components of the type
      --    . invisible components and discriminants of a private ancestor
      --    . invisible components of a derived type

      if Count_Why_Regular_Fields (E) > 0 then
         Count := Count + 1;
      end if;

      --  Directly store the attr__constrained and __tag fields in the record,
      --  as these fields cannot be modified after object creation.

      if Count_Discriminants (E) > 0
        and then Has_Defaulted_Discriminants (E)
      then
         Count := Count + 1;
      end if;

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Top_Level_Fields;

   -------------------------
   -- Create_Zero_Binding --
   -------------------------

   function Create_Zero_Binding
     (Vars : Why_Node_Lists.List;
      Prog : W_Prog_Id) return W_Prog_Id
   is
      Result : W_Prog_Id := Prog;
   begin
      for V of Vars loop
         Result :=
           New_Binding_Ref (Name    => W_Identifier_Id (V),
                            Def     =>
                              +New_Discrete_Constant (Value => Uint_0,
                                                      Typ   => Get_Type (+V)),
                            Context => Result,
                            Typ     => Get_Typ (W_Identifier_Id (V)));
      end loop;
      return Result;
   end Create_Zero_Binding;

   -------------------------------------
   -- Expression_Depends_On_Variables --
   -------------------------------------

   function Expression_Depends_On_Variables (N : Node_Id) return Boolean is

      Variable_Reference_Seen : Boolean := False;

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result;
      --  Attempt to find a variable reference in N

      procedure Search_Variable_Reference is
        new Traverse_Proc (Is_Variable_Reference);

      ---------------------------
      -- Is_Variable_Reference --
      ---------------------------

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result is
      begin
         if Nkind (N) in N_Identifier | N_Expanded_Name
           and then Present (Entity (N))
           and then
             (case Ekind (Entity (N)) is
                 when Object_Kind     => Is_Mutable_In_Why (Entity (N)),
                 when Subprogram_Kind =>
                    Flow_Utility.Has_Proof_Global_Reads (Entity (N),
                                                         Classwide => True),
                 when others          => False)
         then
            Variable_Reference_Seen := True;
            return Abandon;

         --  Continue the traversal

         else
            return OK;
         end if;
      end Is_Variable_Reference;

   --  Start of processing for Expression_Depends_On_Variables

   begin
      Search_Variable_Reference (N);
      return Variable_Reference_Seen;
   end Expression_Depends_On_Variables;

   -----------------------------------
   -- Get_Dispatching_Call_Contract --
   -----------------------------------

   function Get_Dispatching_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Conjuncts_List : Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide => True);
   begin
      if Conjuncts_List.Is_Empty then
         Conjuncts_List := Find_Contracts (E, Kind, Inherited => True);
      end if;

      for Expr of Conjuncts_List loop
         Expr := Dispatching_Contract (Expr);
         pragma Assert (Present (Expr));
      end loop;

      return +Compute_Spec (Params, Conjuncts_List, Domain);
   end Get_Dispatching_Call_Contract;

   function Get_Dispatching_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id is
   begin
      return +Get_Dispatching_Call_Contract (Params, E, Kind, EW_Pred);
   end Get_Dispatching_Call_Contract;

   ----------------------
   -- Get_LSP_Contract --
   ----------------------

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Conjuncts_List : Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide => True);
   begin
      if Conjuncts_List.Is_Empty then
         Conjuncts_List := Find_Contracts (E, Kind, Inherited => True);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, Domain);
   end Get_LSP_Contract;

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id is
   begin
      return +Get_LSP_Contract (Params, E, Kind, EW_Pred);
   end Get_LSP_Contract;

   -----------------------
   -- Get_Graph_Closure --
   -----------------------

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Sets.Set) return Node_Sets.Set
   is
      use Node_Sets;
      Result   : Set;
      Work_Set : Set;
      Cur_Node : Node_Id;
      Cur_Ptr  : Node_Graphs.Cursor;

      Ignored  : Node_Sets.Cursor;
      Inserted : Boolean;

   begin
      Work_Set := From;
      Result := From;

      while not Work_Set.Is_Empty loop
         Cur_Node := Work_Set.First_Element;

         Cur_Ptr := Map.Find (Cur_Node);

         if Node_Graphs.Has_Element (Cur_Ptr) then
            for N of Map (Cur_Ptr) loop
               Result.Insert (New_Item => N,
                              Position => Ignored,
                              Inserted => Inserted);

               if Inserted then
                  Work_Set.Include (N);
               end if;
            end loop;
         end if;

         Work_Set.Delete (Cur_Node);
      end loop;

      return Result;
   end Get_Graph_Closure;

   ---------------------------
   -- Get_Model_Trace_Label --
   ---------------------------

   function Get_Model_Trace_Label
     (E               : Entity_Id;
      Is_Record_Field : Boolean := False;
      Append          : String := "") return Name_Id_Sets.Set
   is
      S : Name_Id_Sets.Set :=
       (Name_Id_Sets.To_Set
          (NID
             (Model_Trace_Label &
              (if E = Empty
               then ""
               else
                 (if Is_Record_Field
                  then "."
                  else "") &
                 Trim (Entity_Id'Image (E), Left) &
                 Append &
               --  Add information whether labels are generated for a
               --  variable holding result of a function.
               (if Ekind (E) = E_Function then "@result" else "")))));
   begin
      S.Include (NID ("name:" & Source_Name (E)));
      return S;
   end Get_Model_Trace_Label;

   ------------------------------
   -- Get_Static_Call_Contract --
   ------------------------------

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Conjuncts_List : constant Node_Lists.List := Find_Contracts (E, Kind);
   begin
      if Conjuncts_List.Is_Empty then
         return Get_LSP_Contract (Params, E, Kind, Domain);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, Domain);
   end Get_Static_Call_Contract;

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id is
   begin
      return +Get_Static_Call_Contract (Params, E, Kind, EW_Pred);
   end Get_Static_Call_Contract;

   -----------------------
   -- Init_Why_Sections --
   -----------------------

   procedure Init_Why_Sections is
      Body_Prefix : constant String := Unit_Name;
   begin
      Why_File_Name := new String'(Body_Prefix & Why_File_Suffix);
      for Kind in W_Section_Id'First ..
                  W_Section_Id'Pred (W_Section_Id'Last)
      loop
         Make_Empty_Why_Section (Kind => Kind, Section => Why_Sections (Kind));
      end loop;
      Make_Empty_Why_Section
        (Kind => WF_Main, Section => Why_Sections (WF_Main));
   end Init_Why_Sections;

   -------------------
   -- Insert_Entity --
   -------------------

   procedure Insert_Entity (E       : Entity_Id;
                            Name    : W_Identifier_Id;
                            Mutable : Boolean := False) is
   begin
      --  For an array in split form, we do not have enough information in Name
      --  to recompute a correct binder.

      pragma Assert
        (not (Get_Typ (Name) /= Why_Empty
         and then Get_Type_Kind (Get_Typ (Name)) = EW_Split
         and then Has_Array_Type (Get_Ada_Node (+Get_Typ (Name)))));

      Ada_Ent_To_Why.Insert (Symbol_Table, E,
                             Mk_Tmp_Item_Of_Entity (E, Name, Mutable));
   end Insert_Entity;

   -----------------
   -- Insert_Item --
   -----------------

   procedure Insert_Item (E : Entity_Id; I : Item_Type) is
   begin
      Ada_Ent_To_Why.Insert (Symbol_Table, E, I);
   end Insert_Item;

   --------------------
   -- Is_Initialized --
   --------------------

   function Is_Initialized
     (Obj   : Entity_Id;
      Scope : Entity_Id)
      return Boolean
   is
   begin
      case Ekind (Scope) is
      --  Inside a subprogram, global variables may be uninitialized if they do
      --  not occur as reads of the subprogram.

      when E_Function | E_Procedure | E_Entry =>

         if Enclosing_Unit (Obj) = Scope
           and then Ekind (Obj) /= E_Out_Parameter
         then
            return True;
         else
            declare
               use Flow_Types;

               Read_Ids  : Flow_Id_Sets.Set;
               Write_Ids : Flow_Id_Sets.Set;

            begin
               Flow_Utility.Get_Proof_Globals (Subprogram     => Scope,
                                               Classwide      => True,
                                               Reads          => Read_Ids,
                                               Writes         => Write_Ids,
                                               Keep_Constants => True);

               --  Elements of Read_Ids have their Variant set to In_View, so
               --  the membership test must also use this variant.

               return Read_Ids.Contains (Direct_Mapping_Id (Obj, In_View));
            end;
         end if;

      --  Every global variable referenced inside a package elaboration must be
      --  initialized. In the same way, tasks can only access synchronized or
      --  Part_Of objects, which are always initialized.

      when E_Package | E_Task_Type =>
         return True;

      when others =>
         raise Program_Error;
      end case;
   end Is_Initialized;

   --------------------------------
   -- Is_Locally_Defined_In_Loop --
   --------------------------------

   function Is_Locally_Defined_In_Loop (N : Node_Id) return Boolean is
      Stmt : Node_Id := Parent (N);
   begin
      while Present (Stmt) loop
         if Nkind (Stmt) = N_Loop_Statement then
            return True;

         elsif Is_Body_Or_Package_Declaration (Stmt) then
            return False;
         end if;

         Stmt := Parent (Stmt);
      end loop;

      return False;
   end Is_Locally_Defined_In_Loop;

   -----------------------
   -- Is_Mutable_In_Why --
   -----------------------

   function Is_Mutable_In_Why (E : Entity_Id) return Boolean is
   begin
      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression).

      if Ekind (E) = E_Loop_Parameter then
         return not Is_Quantified_Loop_Param (E);

      elsif Ekind (E) = E_Variable
        and then Is_Quantified_Loop_Param (E)
      then
         return False;

      --  A component or discriminant is not separately considered as mutable,
      --  only the enclosing object is. This ensures that components used in
      --  the named notation of aggregates are not considered as references
      --  to mutable variables (e.g. in Expression_Depends_On_Variables).

      elsif Ekind (E) in E_Enumeration_Literal |
                         E_Component           |
                         E_Discriminant        |
                         Named_Kind            |
                         Subprogram_Kind       |
                         Entry_Kind
      then
         return False;

      --  Same for objects that have Part_Of specified (for a protected
      --  object), they are like components for proof.

      elsif Is_Part_Of_Protected_Object (E) then
         return False;

      --  Constants defined locally to a loop inside a subprogram (or any
      --  other dynamic scope) may end up having different values, so should
      --  be mutable in Why, except when they are defined inside "actions" (in
      --  which case they are defined as local "let" bound variables in Why)
      --  or when they have no variable inputs.

      elsif Ekind (E) = E_Constant
        and then SPARK_Definition.Is_Loop_Entity (E)
        and then not SPARK_Definition.Is_Actions_Entity (E)
      then
         return Flow_Utility.Has_Variable_Input (E);

      --  We special case any volatile with async writers: they are always
      --  mutable (even if they are, for example, in parameters). Constants
      --  cannot be volatile in SPARK so are not considered here.

      elsif Ekind (E) /= E_Constant
        and then Has_Volatile (E)
        and then Has_Volatile_Flavor (E, Pragma_Async_Writers)
      then
         return True;

      elsif Is_Constant_Object (E) then
         return False;

      else
         return True;
      end if;
   end Is_Mutable_In_Why;

   ----------------------------
   -- Is_Simple_Private_Type --
   ----------------------------

   function Is_Simple_Private_Type (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Retysp (E);
   begin
      return Is_Private_Type (Ty)
        and then Count_Discriminants (Ty) = 0
        and then not Is_Tagged_Type (Ty);
   end Is_Simple_Private_Type;

   ----------------------------
   -- Make_Empty_Why_Section --
   ----------------------------

   procedure Make_Empty_Why_Section
     (Kind : W_Section_Id; Section : out Why_Section) is
   begin
      Section.Kind := Kind;
      Section.Theories := Why_Node_Lists.Empty_List;
      Section.Cur_Theory := Why.Types.Why_Empty;
   end Make_Empty_Why_Section;

   ---------------------------
   -- May_Need_DIC_Checking --
   ---------------------------

   function May_Need_DIC_Checking (E : Entity_Id) return Boolean is
      DIC_Needs_To_Be_Checked : constant Boolean :=
        Has_Own_DIC (E)
        and then Present (DIC_Procedure (E));

      DIC_Needs_To_Be_Rechecked : constant Boolean :=
        Is_Tagged_Type (E)
        and then Is_Full_View (E)
        and then Present (DIC_Procedure (E))
        and then Expression_Contains_Primitives_Calls_Of
          (Get_Expr_From_Check_Only_Proc (DIC_Procedure (E)), E);
   begin
      return DIC_Needs_To_Be_Checked or DIC_Needs_To_Be_Rechecked;
   end May_Need_DIC_Checking;

   -----------------------------
   -- Needs_DIC_Check_At_Decl --
   -----------------------------

   function Needs_DIC_Check_At_Decl (Ty : Entity_Id) return Boolean is
      E : constant Entity_Id := Retysp (Ty);
   begin
      return May_Need_DIC_Checking (E)
        and then not Is_Private_Type (E)
        and then Present (Get_Initial_DIC_Procedure (E))
        and then Check_DIC_At_Declaration (E);
   end Needs_DIC_Check_At_Decl;

   ----------------------------
   -- Needs_DIC_Check_At_Use --
   ----------------------------

   function Needs_DIC_Check_At_Use (Ty : Entity_Id) return Boolean is
     (Present (DIC_Procedure (Ty))
       and then Present (Get_Initial_DIC_Procedure (Ty))
       and then not Check_DIC_At_Declaration (Ty));

   --------------------------------
   -- Nth_Index_Rep_Type_No_Bool --
   --------------------------------

   function Nth_Index_Rep_Type_No_Bool (E : Entity_Id; Dim : Positive)
                                        return W_Type_Id
   is
     (Base_Why_Type_No_Bool
        (Nth_Index_Type
           ((if Ekind (E) = E_String_Literal_Subtype
             --  If E is a string literal subtype then use its base type's
             --  index type type's.
             then Retysp (Etype (E))
             else E),
            Dim)));

   ----------------
   -- Short_Name --
   ----------------

   function Short_Name (E : Entity_Id) return String is
     (Avoid_Why3_Keyword (Get_Name_String (Chars (E))));

   -----------------------------
   -- Type_Is_Modeled_As_Base --
   -----------------------------

   function Type_Is_Modeled_As_Base (T : Entity_Id) return Boolean is
   begin
      return Is_Scalar_Type (T)
        and then (not Has_Static_Scalar_Subtype (T)
                  or else Is_Null_Range (T));
   end Type_Is_Modeled_As_Base;

   ----------------------------------
   -- Type_Needs_Dynamic_Invariant --
   ----------------------------------

   function Type_Needs_Dynamic_Invariant (T : Entity_Id) return Boolean is
      function Has_Potentially_Inherited_Type_Invariants
        (T : Entity_Id) return Boolean;
      --  Return True if T or one of its ancestors has a type invariant

      function Type_Needs_Dynamic_Invariant
        (T         : Entity_Id;
         Top_Level : Boolean) return Boolean;
      --  Generation of dynamic invariants is slightly different when called
      --  recursively on component types of arrays or records. Top_Level should
      --  be False in recursive calls.

      -----------------------------------------------
      -- Has_Potentially_Inherited_Type_Invariants --
      -----------------------------------------------

      function Has_Potentially_Inherited_Type_Invariants
        (T : Entity_Id) return Boolean
      is
         Current : Entity_Id := T;
         Parent  : Entity_Id;
      begin
         loop
            if Has_Invariants_In_SPARK (Current) then
               return True;
            end if;

            if Full_View_Not_In_SPARK (Current) then
               Parent := Get_First_Ancestor_In_SPARK (Current);
            else
               Parent := Retysp (Etype (Current));
            end if;
            exit when Current = Parent;
            Current := Parent;
         end loop;
         return False;
      end Has_Potentially_Inherited_Type_Invariants;

      ----------------------------------
      -- Type_Needs_Dynamic_Invariant --
      ----------------------------------

      function Type_Needs_Dynamic_Invariant
        (T         : Entity_Id;
         Top_Level : Boolean) return Boolean
      is
         Ty_Ext : constant Entity_Id := Retysp (T);

      begin
         --  Dynamic invariant of the type itself

         --  If the type is modeled as its base type, we need an invariant for
         --  its specific subtype constraint.

         if Type_Is_Modeled_As_Base (Ty_Ext)

           --  If the type is represented in split form, we need the invariant
           --  but not for components of arrays and records which are never
           --  represented in split form.

           or else (Top_Level and then Use_Split_Form_For_Type (Ty_Ext))

           --  For non static array types, we need an invariant to state the
           --  ranges of bounds.

           or else (Is_Array_Type (Ty_Ext)
                     and then not Is_Static_Array_Type (Ty_Ext))

           --  For constrained types with discriminants, we supply the value
           --  of the discriminants.

           or else (Count_Discriminants (Ty_Ext) > 0
                     and then Is_Constrained (Ty_Ext))

           --  For component types with defaulted discriminants, we know the
           --  discriminants have their default value.

           or else (not Top_Level
                     and then Count_Discriminants (Ty_Ext) > 0
                     and then Has_Defaulted_Discriminants (Ty_Ext))

           --  We need an invariant for type predicates

           or else Has_Predicates (Ty_Ext)

           --  We need an invariant for type invariants

           or else Has_Potentially_Inherited_Type_Invariants (Ty_Ext)
         then
            return True;
         end if;

         --  For composite types, check for dynamic invariants on components

         if Is_Array_Type (Ty_Ext)
           and then Ekind (Ty_Ext) /= E_String_Literal_Subtype
         then
            return
              Type_Needs_Dynamic_Invariant (Component_Type (Ty_Ext), False);

         elsif Is_Record_Type (Ty_Ext)
           or else Is_Private_Type (Ty_Ext)
           or else Is_Concurrent_Type (Ty_Ext)
         then
            if Count_Discriminants (Ty_Ext) > 0 then
               declare
                  Discr : Entity_Id := First_Discriminant (Ty_Ext);
               begin
                  while Present (Discr) loop
                     if Type_Needs_Dynamic_Invariant (Etype (Discr), False)
                     then
                        return True;
                     end if;
                     Next_Discriminant (Discr);
                  end loop;
               end;
            end if;

            for Comp of Get_Component_Set (Ty_Ext) loop
               if not Is_Type (Comp)
                 and then Type_Needs_Dynamic_Invariant (Etype (Comp), False)
               then
                  return True;
               end if;
            end loop;
         end if;

         return False;
      end Type_Needs_Dynamic_Invariant;

   --  Start of processing for Type_Needs_Dynamic_Invariant

   begin
      return Type_Needs_Dynamic_Invariant (T, True);
   end Type_Needs_Dynamic_Invariant;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
      T : constant Entity_Id :=
        (case Nkind (N) is
            when N_Entity =>
              (if Is_Type (N) then
                 N
               else
                 Etype (N)),
            when N_Identifier | N_Expanded_Name =>
               Etype (Entity (N)),
            when others =>
               Etype (N));

   begin
      --  The type of a node is either its most underlying type, or else the
      --  special private type in all other cases, represented in the AST by
      --  its type.

      return (case Ekind (T) is
                 when Type_Kind => Retysp (T),
                 when others => T);
   end Type_Of_Node;

   ----------------------------
   -- Use_Guard_For_Function --
   ----------------------------

   function Use_Guard_For_Function (E : Entity_Id) return Boolean is
   begin
      return Gnat2Why_Args.Proof_Generate_Guards

        --  No axioms are generated for functions with No_Return

        and then not No_Return (E)

        --  No axioms are generated for volatile functions

        and then not
          (Is_Volatile_Function (E)
            and then not Within_Protected_Type (E))

        --  No axioms are generated for inlined functions

        and then not Present (Gnat2Why.Annotate.Retrieve_Inline_Annotation (E))

        --  Functions from predefined units should be safe

        and then not Lib.In_Predefined_Unit (E)

        --  No axioms are generated for functions with external axiomatizations

        and then not Entity_In_Ext_Axioms (E);
   end Use_Guard_For_Function;

   -----------------------------
   -- Use_Split_Form_For_Type --
   -----------------------------

   function Use_Split_Form_For_Type (E : Entity_Id) return Boolean is
   begin
      return (Is_Discrete_Type (Retysp (E))
              or else Is_Floating_Point_Type (Retysp (E)))
        and then not Is_Standard_Boolean_Type (Retysp (E));
   end Use_Split_Form_For_Type;

   ------------------------
   -- Why_Type_Of_Entity --
   ------------------------

   function Why_Type_Of_Entity (E : Entity_Id) return W_Type_Id is
   begin

      --  Entities for ASCII characters are not translated. Instead we use
      --  directly their integer translation.

      if Sloc (E) = Standard_ASCII_Location then
         return EW_Int_Type;
      else
         declare
            Binder : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, E);
         begin
            return Get_Why_Type_From_Item (Binder);
         end;
      end if;
   end Why_Type_Of_Entity;

   -----------------------
   -- Why_Type_Is_Float --
   -----------------------

   function Why_Type_Is_Float (Typ : W_Type_Id) return Boolean is
   begin
      return Typ in EW_Float_32_Type .. EW_Float_64_Type;
   end Why_Type_Is_Float;

   ---------------------------
   -- Why_Type_Is_BitVector --
   ---------------------------

   function Why_Type_Is_BitVector (Typ : W_Type_Id) return Boolean is
   begin
      return Typ in EW_BitVector_8_Type  |
                    EW_BitVector_16_Type |
                    EW_BitVector_32_Type |
                    EW_BitVector_64_Type;
   end Why_Type_Is_BitVector;

begin
   Why3_Keywords.Include ("as");
   Why3_Keywords.Include ("abstract");
   Why3_Keywords.Include ("absurd");
   Why3_Keywords.Include ("any");
   Why3_Keywords.Include ("assert");
   Why3_Keywords.Include ("assume");
   Why3_Keywords.Include ("axiom");
   Why3_Keywords.Include ("begin");
   Why3_Keywords.Include ("bool");
   Why3_Keywords.Include ("by");
   Why3_Keywords.Include ("check");
   Why3_Keywords.Include ("clone");
   Why3_Keywords.Include ("coinductive");
   Why3_Keywords.Include ("constant");
   Why3_Keywords.Include ("do");
   Why3_Keywords.Include ("done");
   Why3_Keywords.Include ("downto");
   Why3_Keywords.Include ("else");
   Why3_Keywords.Include ("end");
   Why3_Keywords.Include ("epsilon");
   Why3_Keywords.Include ("exception");
   Why3_Keywords.Include ("exists");
   Why3_Keywords.Include ("export");
   Why3_Keywords.Include ("false");
   Why3_Keywords.Include ("for");
   Why3_Keywords.Include ("forall");
   Why3_Keywords.Include ("fun");
   Why3_Keywords.Include ("function");
   Why3_Keywords.Include ("ghost");
   Why3_Keywords.Include ("goal");
   Why3_Keywords.Include ("if");
   Why3_Keywords.Include ("import");
   Why3_Keywords.Include ("in");
   Why3_Keywords.Include ("inductive");
   Why3_Keywords.Include ("int");
   Why3_Keywords.Include ("invariant");
   Why3_Keywords.Include ("lemma");
   Why3_Keywords.Include ("let");
   Why3_Keywords.Include ("loop");
   Why3_Keywords.Include ("match");
   Why3_Keywords.Include ("meta");
   Why3_Keywords.Include ("model");
   Why3_Keywords.Include ("module");
   Why3_Keywords.Include ("mutable");
   Why3_Keywords.Include ("namespace");
   Why3_Keywords.Include ("not");
   Why3_Keywords.Include ("old");
   Why3_Keywords.Include ("predicate");
   Why3_Keywords.Include ("private");
   Why3_Keywords.Include ("prop");
   Why3_Keywords.Include ("private");
   Why3_Keywords.Include ("raise");
   Why3_Keywords.Include ("raises");
   Why3_Keywords.Include ("reads");
   Why3_Keywords.Include ("rec");
   Why3_Keywords.Include ("real");
   Why3_Keywords.Include ("result");
   Why3_Keywords.Include ("returns");
   Why3_Keywords.Include ("so");
   Why3_Keywords.Include ("then");
   Why3_Keywords.Include ("theory");
   Why3_Keywords.Include ("to");
   Why3_Keywords.Include ("try");
   Why3_Keywords.Include ("true");
   Why3_Keywords.Include ("type");
   Why3_Keywords.Include ("unit");
   Why3_Keywords.Include ("use");
   Why3_Keywords.Include ("val");
   Why3_Keywords.Include ("variant");
   Why3_Keywords.Include ("while");
   Why3_Keywords.Include ("with");
   Why3_Keywords.Include ("writes");
end Gnat2Why.Util;
