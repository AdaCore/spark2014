------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2016, AdaCore                  --
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

with Ada.Strings;            use Ada.Strings;
with Ada.Strings.Fixed;      use Ada.Strings.Fixed;
with Flow_Types;
with Flow_Utility;
with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Sem_Util;               use Sem_Util;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with String_Utils;           use String_Utils;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Modules;      use Why.Atree.Modules;
with Why.Conversions;        use Why.Conversions;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Inter;              use Why.Inter;
with Why.Types;              use Why.Types;

package body Gnat2Why.Util is

   Why3_Keywords : String_Utils.String_Sets.Set;

   procedure Make_Empty_Why_Section
     (Kind : W_Section_Id; Section : out Why_Section)
     with Post => (Section.Cur_Theory = Why.Types.Why_Empty);
   --  Return an empty Why_Section with the given kind

   --------------------
   -- Ada_Ent_To_Why --
   --------------------

   package body Ada_Ent_To_Why is

      -------------
      -- Element --
      -------------

      function Element (M : Map; E : Entity_Id) return Item_Type is
      begin
         return M.Entity_Ids.Element (E);
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
         C : constant Ent_To_Why.Cursor := M.Entity_Ids.Find (E);
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
               Ent : constant Entity_Id := Find_Entity (E);
            begin
               if Present (Ent) then
                  return Find (M, Ent);
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

      function Has_Element (M : Map; E : Entity_Id) return Boolean
      is
      begin
         return M.Entity_Ids.Contains (E);
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
         C : Ent_To_Why.Cursor;
         Inserted : Boolean;
      begin
         M.Entity_Ids.Insert (E, W, C, Inserted);
         if Undo_Stacks.Is_Empty (M.Undo_Stack) then

            --  At the global level (no undo stack) we expect that there are no
            --  clashes in symbols

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Ent, E));
            else

               --  If there was already an entry for the entity, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted

               M.Undo_Stack.Append
                 (Action'(Kind       => Insert_Ent,
                          Ins_Entity => Ent_To_Why.Key (C),
                          Ins_Binder => Ent_To_Why.Element (C)));
               M.Entity_Ids.Replace (E, W);
               M.Undo_Stack.Append (Action'(Remove_Ent, E));
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
               --  reinserted

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
      Labels : Name_Id_Sets.Set := Name_Id_Sets.Empty_Set;
      Model_Trace : constant Name_Id_Sets.Set := Get_Model_Trace_Label
        (E, False, Append_To_Name);
   begin
      --  Currently only generate values for scalar, record, and array
      --  variables in counterexamples.

      if (not Comes_From_Source (E) and then
            not Comes_From_Source (Parent (E)))
          or else
            (Is_Floating_Point_Type (Etype (E)))
      then
         return Name_Id_Sets.Empty_Set;
      end if;

      if Is_Scalar_Type (Etype (E)) then
         Labels.Union (Model_Trace);

         --  If E's type is directly a native prover type, simply request the
         --  value of E in the counterexample. This is known by querying the
         --  kind of type used in Why3 for the entity. If it's not abstract,
         --  then a builtin Why3 type is used.

         if Get_Type_Kind (Type_Of_Node (Etype (E))) in EW_Builtin | EW_Split
         then
            Labels.Include (Model);

         --  If E's type needs a projection to a native prover type, request
         --  the value of the projection of E in the counterexample.

         else
            Labels.Include (Model_Projected);
         end if;
      end if;

      if Is_Record_Type (Etype (E)) then
         Labels.Union (Model_Trace);
         Labels.Include (Model_Projected);
      end if;

      if Is_Array_Type (Etype (E)) then
         Labels.Union (Model_Trace);
         Labels.Include (Model_Projected);
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
      Kind      : Name_Id;
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
           New_Binding_Ref (Name     => W_Identifier_Id (V),
                            Def      =>
                              +New_Discrete_Constant (Value => Uint_0,
                                                      Typ   => Get_Type (+V)),
                            Context  => Result,
                            Typ      => Get_Typ (W_Identifier_Id (V)));
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
      Kind   : Name_Id;
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
      Kind   : Name_Id) return W_Pred_Id is
   begin
      return +Get_Dispatching_Call_Contract (Params, E, Kind, EW_Pred);
   end Get_Dispatching_Call_Contract;

   ----------------------
   -- Get_LSP_Contract --
   ----------------------

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
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
      Kind   : Name_Id) return W_Pred_Id is
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
      Append : String := "") return Name_Id_Sets.Set
   is
     (Name_Id_Sets.To_Set
        (NID
           (Model_Trace_Label &
            (if E = Empty
             then ""
             else
               (if Is_Record_Field
                then "."
                else "") &
                Trim (Entity_Id'Image (E), Both) &
                Append &
                --  Add information whether labels are generated for a
                --  variable holding result of a function.
                (if Ekind (E) = E_Function then "@result" else "")))));

   ------------------------------
   -- Get_Static_Call_Contract --
   ------------------------------

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
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
      Kind   : Name_Id) return W_Pred_Id is
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

   function Is_Mutable_In_Why (N : Node_Id) return Boolean is
   begin
      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression).

      if Ekind (N) = E_Loop_Parameter then
         return not (Is_Quantified_Loop_Param (N));

      elsif Ekind (N) = E_Variable
        and then Is_Quantified_Loop_Param (N)
      then
         return False;

      --  A component or discriminant is not separately considered as mutable,
      --  only the enclosing object is. This ensures that components used in
      --  the named notation of aggregates are not considered as references
      --  to mutable variables (e.g. in Expression_Depends_On_Variables).

      elsif Ekind (N) in E_Enumeration_Literal |
                         E_Component           |
                         E_Discriminant        |
                         Named_Kind            |
                         Subprogram_Kind       |
                         Entry_Kind
      then
         return False;

      --  Same for objects that have Part_Of specified (for a protected
      --  object), they are like components for proof.

      elsif Is_Part_Of_Protected_Object (N) then
         return False;

      --  Constants defined locally to a loop inside a subprogram (or any
      --  other dynamic scope) may end up having different values, so should
      --  be mutable in Why, except when they are defined inside "actions" (in
      --  which case they are defined as local "let" bound variables in Why).

      elsif Ekind (N) = E_Constant
        and then SPARK_Definition.Is_Loop_Entity (N)
        and then not SPARK_Definition.Is_Actions_Entity (N)
      then
         return True;

      --  We special case any volatile with async writers: they are always
      --  mutable (even if they are, for example, in parameters). Constants
      --  cannot be volatile in SPARK so are not considered here.

      elsif Ekind (N) /= E_Constant
        and then
          Flow_Types.Has_Async_Writers (Flow_Types.Direct_Mapping_Id (N))
      then
         return True;

      elsif Is_Constant_Object (N) then
         return False;

      else
         return True;
      end if;
   end Is_Mutable_In_Why;

   -------------------------
   -- Make_Empty_Why_File --
   -------------------------

   procedure Make_Empty_Why_Section
     (Kind : W_Section_Id; Section : out Why_Section) is
   begin
      Section.Kind := Kind;
      Section.Theories := Why_Node_Lists.Empty_List;
      Section.Cur_Theory := Why.Types.Why_Empty;
   end Make_Empty_Why_Section;

   ----------------
   -- Short_Name --
   ----------------

   function Short_Name (E : Entity_Id) return String
   is
   begin
      return Avoid_Why3_Keyword (Get_Name_String (Chars (E)));
   end Short_Name;

   --------------------------------
   -- Nth_Index_Rep_Type_No_Bool --
   --------------------------------

   function Nth_Index_Rep_Type_No_Bool (E : Entity_Id; Dim : Positive)
                                        return W_Type_Id
   is
   begin
      if Ekind (E) = E_String_Literal_Subtype then

         --  If E is a string literal subtype use its base type's index type

         return
           Base_Why_Type_No_Bool (Nth_Index_Type (Retysp (Etype (E)), Dim));
      else
         return (Base_Why_Type_No_Bool (Nth_Index_Type (E, Dim)));
      end if;
   end Nth_Index_Rep_Type_No_Bool;

   -----------------------------
   -- Type_Is_Modeled_As_Base --
   -----------------------------

   function Type_Is_Modeled_As_Base (T : Entity_Id) return Boolean is
   begin
      return Is_Scalar_Type (T) and then
        (not Has_Static_Scalar_Subtype (T) or else
         Is_Null_Range (T));
   end Type_Is_Modeled_As_Base;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return Entity_Id is
      T : constant Entity_Id :=
        (case Nkind (N) is
            when N_Entity =>
              (if Ekind (N) in Type_Kind then
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
   -- Use_Base_Type_For_Type --
   ----------------------------

   function Use_Base_Type_For_Type (E : Entity_Id) return Boolean is
   begin
      return Is_Scalar_Type (E) and then
        not Is_Standard_Boolean_Type (E);
   end Use_Base_Type_For_Type;

   -----------------------------
   -- Use_Split_From_For_Type --
   -----------------------------

   function Use_Split_Form_For_Type (E : Entity_Id) return Boolean is
   begin
      return Is_Discrete_Type (Retysp (E)) and then
        not Is_Standard_Boolean_Type (Retysp (E));
   end Use_Split_Form_For_Type;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E) and then
        Use_Base_Type_For_Type (Ty);
   end Use_Why_Base_Type;

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
