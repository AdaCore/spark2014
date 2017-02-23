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

with Ada.Strings;            use Ada.Strings;
with Ada.Strings.Fixed;      use Ada.Strings.Fixed;
with Eval_Fat;
with Exp_Util;               use Exp_Util;
with Flow_Types;
with Flow_Utility;
with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Gnat2Why.Tables;        use Gnat2Why.Tables;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Aux;                use Sem_Aux;
with Sem_Util;               use Sem_Util;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with Stand;                  use Stand;
with String_Utils;           use String_Utils;
with Urealp;                 use Urealp;
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
            --  clashes in symbols.

            pragma Assert (Inserted);
         else
            if Inserted then
               M.Undo_Stack.Append (Action'(Remove_Ent, E));
            else

               --  If there was already an entry for the entity, we need to
               --  store in the undo stack the fact that this info must be
               --  reinserted.

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
      Labels : Name_Id_Sets.Set;
      Model_Trace : constant Name_Id_Sets.Set := Get_Model_Trace_Label
        (E, False, Append_To_Name);

      E_Type : constant Entity_Id := Retysp (Etype (E));
      --  Taking the full_view of the type to be able to match private
      --  type in the same way as other types because the current intended
      --  behavior is to print private types as if they were public.

   begin
      --  Currently generate non-empty set of labels values only for variables
      --  of scalar, record, and array types. For variables of other types,
      --  getting counterexample values is not supported.

      if (not Comes_From_Source (E)
            and then not Comes_From_Source (Parent (E)))
        or else
          Is_Floating_Point_Type (Etype (E))
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

      if Has_Discriminants (E) then
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

      if Has_Defaulted_Discriminants (E) then
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

   ------------------------
   --  Cast_Real_Literal --
   ------------------------

   function Cast_Real_Literal (E  : Node_Id;
                               Ty : W_Type_Id) return W_Integer_Constant_Id
   is
      function Ureal_To_Bitstream (Rval : Ureal; Ty : W_Type_Id) return Uint;
      --  This function returns the bit representation of a float as an integer
      --  constant. Note that it is not returned as a bit-vector in order to
      --  not have systematically a theory of bit-vectors in the context
      --  whenever a float literal appears in a VC.
      --  @param Rval The real value of the float, it is expected to be rounded
      --  @param Ty The type of the float, either EW_Float_32_Type or
      --         EW_Float_64_Type
      --  @return An integer constant with the same bit representation as the
      --          float constant.

      function Ureal_To_Bitstream
        (Rval : Ureal;
         Ty   : W_Type_Id) return Uint
      is
         Base : constant Nat := Rbase (Rval);
         Den  : Uint := Denominator (Rval);
         Num  : Uint := Numerator (Rval);

         --  Rval = num * Base ** (- Den)

         --  This code is not complete with regard to the frontend, we only
         --  accept the "format" described below and will raise an error if it
         --  is not the case. Those constraints are based on what the frontend
         --  as given us so far. This needs to be completed !!!

         --  We expect the frontend to give us Rval in a format such that :
         --  - Base is either 2 or 16 (exept for 0 in base 10)
         --  - Den is greater to ebias + sig_size - 1
         --    or equal if Rval is a denormal
         --  - Num is smaller than Base**(Sig_Size+1)
         --  - Num is greater than Base**Sig_Size if Rval is normal
         --  All other cases should raise an error

         --  Denormal of base 16 are not treated as they apparently are not
         --  provided by the frontend

         --  Next we consider the exponent bias (= max exponent value) and the
         --  size of the significand defined in the IEEE format, i.e.,
         --  for 32 bit floats we have:
         --  + 24 bits, counting the hidden bit, in the mantissa,
         --  + 8 exponent bits, the exponent bias is then 2 ** 7 - 1 = 127.
         --  For 64 bit floats we have:
         --  + 53 bits, counting the hidden bit, in the mantissa,
         --  + 11 exponent bits, the exponent bias is then 2 ** 10 - 1 = 1023.

         Ebias : constant Nat := (if Ty = EW_Float_32_Type then
                                    127
                                 else
                                    1023);

         --  the exponent bias

         Sig_Size : constant Nat := (if Ty = EW_Float_32_Type then
                                        23
                                     else
                                        52);

         --  the size of the significand (or mantissa)

         Size : constant Int := (if Ty = EW_Float_32_Type
                                 then 32
                                 else 64);

         --  the bit of sign

         Sign_Bit : constant Uint := (if UR_Is_Negative (Rval) then
                                         UI_Expon (Uint_2, Size - 1)
                                      else Uint_0);

         --  the value of the exponent for subnormals

         Subnormal_Exp : constant Uint := Ebias - Uint_1 + Sig_Size;

         Exppat : Uint;
         Bitpat : Uint;
      begin

         --  Deal with zero first as it is an easy case

         if UR_Eq (Rval, Ureal_0) then
            return Sign_Bit;
         end if;

         --  Fail on unexpected base

         if Base not in 2 | 10 | 16 then
            raise Program_Error;
         end if;

         --  Check that Num fit inside the significand.

         if (Base = 2 and UI_Ge (Num, UI_Expon (Uint_2, Sig_Size + 1)))
           or else
            (Base = 16 and
             UI_Ge (Num, UI_Expon (Uint_16, (Sig_Size / 4) + 1)))
         then
            raise Program_Error;
         end if;

         --  Now deal with the remaining cases

         if Base = 10 then

            --  In case of base 10 rval we recast it in base 2 through
            --  Eval_Fat.Machine and don't directly send the pattern
            --  in order to check it with the original rval in base 10.
            --  This will most probably be incorrect for subnormals !
            --  ??? Investigate which cases need this treatment

            Bitpat := Ureal_To_Bitstream
              (Rval  => Eval_Fat.Machine (RT    => (if Ty = EW_Float_32_Type
                                                    then Standard_Float
                                                    else Standard_Long_Float),
                                          X     => Rval,
                                          Mode  => Eval_Fat.Round_Even,
                                          Enode => E),
               Ty => Ty);

         elsif Base = 2 and (UI_Lt (Num, UI_Expon (Uint_2, Sig_Size)))
         then

            --  We deal with subnormals for base 2

            if not UI_Eq (Den, Subnormal_Exp) then

               --  If Rval is not in the expected form, raise an error

               raise Program_Error;
            end if;

            Bitpat := Num + Sign_Bit;

         elsif Base = 2 and (UI_Gt (Den, Subnormal_Exp)) then

            --  second format for subnormals

            --  Here we expect subnormal of the form
            --    2^sig_size <= Num < 2^(sig_size+1)
            --    Ebias + 2 * Sig_Size - 1 >= Den > Ebias + Sig_Size
            --  for example
            --  Succ'(0.0) = 2^sig_size * 2^-(Ebias + 2 * sig_size - 1)

            declare
               Max_Den : constant Uint := Ebias + 2 * Sig_Size - Uint_1;
            begin
               pragma Assert (UI_Le (Den, Max_Den));

               Bitpat := UI_Div (Num,
                                 UI_Expon (Uint_2, Den - Subnormal_Exp));

               pragma Assert
                 (Num = Bitpat * UI_Expon (Uint_2, Den - Subnormal_Exp));
            end;

         elsif Base = 16 and (UI_Lt (Num, UI_Expon (Uint_2, Sig_Size)))
         then

            --  subnormal of base 16 are not expected

            raise Program_Error;

         else

            --  We're left to deal with normals

            --  invert the sign of the exponent : we want a multiplication,
            --  not a division.

            Den := UI_Negate (Den);

            --  change of base for rval of base 16

            if Base = 16 then
               Den := UI_Mul (Uint_4, Den);

               --  in this case it happens that num is bigger than
               --  2 ^ (sig_size + 1), in which case we divide it by two until
               --  we get num in the expected range.

               while UI_Ge (Num, UI_Expon (Uint_2, Sig_Size + 1)) loop
                  Num := UI_Div (Num, Uint_2);
                  Den := UI_Add (Den, Uint_1);
               end loop;

               if UI_Le (Den, -(Ebias + Sig_Size)) then

                  --  check that we're not dealing with a subnormal value

                  raise Program_Error;

               end if;
            end if;

            --  compute the pattern for the exponent

            Exppat := Ebias + Den + Sig_Size;

            --  remove the implicit most significand bit of the significand

            Bitpat := (Num - UI_Expon (Uint_2, Sig_Size));

            --  add the exponent pattern and sign bit to complete the bit
            --  pattern

            Bitpat := Bitpat
              + Exppat * UI_Expon (Uint_2, Sig_Size)
              + Sign_Bit;

         end if;

         pragma Assert (0 <= Bitpat and Bitpat < UI_Expon (2, Size));

         declare
            --  Here we compute back the real value from the pattern that we
            --  just produced in order to add some guaranty to this process.

            --  the bit of sign

            NB : constant Uint := UI_Div (Bitpat, UI_Expon (Uint_2, Size - 1));

            --  the exponent

            D  : constant Uint := UI_Div (Bitpat - UI_Mul (NB,
                                          UI_Expon (Uint_2, Size - 1)),
                                          UI_Expon (Uint_2, Sig_Size));

            --  the significand

            N  : constant Uint := Bitpat
              - UI_Mul (NB, UI_Expon (Uint_2, Size - 1))
              - UI_Mul (D,  UI_Expon (Uint_2, Sig_Size));

            --  to compute the real value there are two cases:
            --  + either D is zero, which means that the value is subnormal
            --    since we allready dealt with zero;
            --  + or it is not, in which case we have a normal value.

            Bitpat_R : constant Ureal :=
              (if UI_Eq (D, Uint_0) then
                    UR_From_Components
                 (Num      => N,
                  Den      => Subnormal_Exp,
                  Rbase    => 2,
                  Negative => (NB = 1))
               else
                  UR_From_Components
                 (Num      => N + UI_Expon (Uint_2, Sig_Size),
                  Den      => -(D - Ebias - Sig_Size),
                  Rbase    => 2,
                  Negative => (NB = 1)));
         begin

            --  let's look for some guaranty of correctness !

            if not (UR_Eq (Rval, Bitpat_R)) then
               raise Program_Error;
            end if;
         end;

         return Bitpat;

      end Ureal_To_Bitstream;

   begin
      return New_Integer_Constant
        (Ada_Node => E,
         Value    => Ureal_To_Bitstream (Rval => Realval (E),
                                         Ty   => Ty));
   end Cast_Real_Literal;

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

           or else (Has_Discriminants (Ty_Ext)
                     and then Is_Constrained (Ty_Ext))

           --  For component types with defaulted discriminants, we know the
           --  discriminants have their default value.

           or else (not Top_Level
                     and then Has_Discriminants (Ty_Ext)
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

         elsif Is_Record_Type (Ty_Ext) or else Is_Private_Type (Ty_Ext) then
            if Has_Discriminants (Ty_Ext) then
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
      return Is_Scalar_Type (E)
        and then not Is_Standard_Boolean_Type (E);
   end Use_Base_Type_For_Type;

   -----------------------------
   -- Use_Split_From_For_Type --
   -----------------------------

   function Use_Split_Form_For_Type (E : Entity_Id) return Boolean is
   begin
      return (Is_Discrete_Type (Retysp (E))
              or else Is_Floating_Point_Type (Retysp (E)))
        and then not Is_Standard_Boolean_Type (Retysp (E));
   end Use_Split_Form_For_Type;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E)
        and then Use_Base_Type_For_Type (Ty);
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
