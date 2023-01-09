------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2012-2023, AdaCore                     --
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
with Ada.Unchecked_Deallocation;
with Atree;
with Flow_Generated_Globals.Phase_2;
with Flow_Types;
with Flow_Utility;
with GNATCOLL.Symbols;           use GNATCOLL.Symbols;
with Gnat2Why_Args;
with Gnat2Why.Expr;              use Gnat2Why.Expr;
with SPARK_Util.Subprograms;     use SPARK_Util.Subprograms;
with Nlists;                     use Nlists;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Definition.Annotate;  use SPARK_Definition.Annotate;
with String_Utils;               use String_Utils;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Inter;                  use Why.Inter;
with Why.Keywords;               use Why.Keywords;

package body Gnat2Why.Util is

   Why3_Keywords : String_Utils.String_Sets.Set;

   procedure Make_Empty_Why_Section (Section : out Why_Section);

   --------------------
   -- Ada_Ent_To_Why --
   --------------------

   package body Ada_Ent_To_Why is

      function Normalize_Entity (E : Entity_Id) return Entity_Id is
        (if Nkind (E) in N_Entity and then Ekind (E) = E_Discriminant then
              Root_Discriminant (E) else E);
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
            return Cursor'(CK_Ent, Ent_To_Why.No_Element,
                           Name_To_Why_Map.No_Element);
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

      procedure Insert
        (M : in out Map;
         E :        Entity_Id;
         W :        Item_Type)
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

      procedure Insert
        (M : in out Map;
         E :        Entity_Name;
         W :        Item_Type)
      is
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

         procedure Apply_Action (A : Action);
         --  Apply a single action

         ------------------
         -- Apply_Action --
         ------------------

         procedure Apply_Action (A : Action) is
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
         while Undo_Stacks.Has_Element (C)
           and then M.Undo_Stack (C).Kind /= Boundary
         loop
            Apply_Action (M.Undo_Stack (C));
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

   ----------------------
   -- Get_Base_Of_Type --
   ----------------------

   function Get_Base_Of_Type (T : Type_Kind_Id) return Type_Kind_Id is
      Ty : Type_Kind_Id := Retysp (T);
   begin
      loop
         exit when not Type_Is_Modeled_As_Base (Ty);
         Ty := Retysp (Etype (Ty));
      end loop;
      return Ty;
   end Get_Base_Of_Type;

   ----------------------------
   -- Get_Borrows_From_Decls --
   ----------------------------

   procedure Get_Borrows_From_Decls
     (Decls   :        List_Id;
      Borrows : in out Node_Lists.List)
   is
      Cur_Decl : Node_Id := First (Decls);
   begin
      while Present (Cur_Decl) loop
         if Nkind (Cur_Decl) = N_Object_Declaration then
            declare
               E : constant Constant_Or_Variable_Kind_Id :=
                 Defining_Identifier (Cur_Decl);
            begin
               if Is_Local_Borrower (E) then
                  Borrows.Prepend (E);
               end if;
            end;
         end if;
         Next (Cur_Decl);
      end loop;
   end Get_Borrows_From_Decls;

   ---------------------------------------------
   -- Get_Container_In_Iterator_Specification --
   ---------------------------------------------

   function Get_Container_In_Iterator_Specification
     (N : Node_Id)
      return Node_Id
   is
      Iter : constant Node_Id := SPARK_Atree.Name (N);
   begin
      return (Iter);
   end Get_Container_In_Iterator_Specification;

   -------------------------------
   -- Get_Counterexample_Labels --
   -------------------------------

   function Get_Counterexample_Labels
     (E              : Entity_Id;
      Append_To_Name : String := "")
      return Symbol_Sets.Set
   is
      Labels : Symbol_Sets.Set;
      Model_Trace : constant Symbol_Sets.Set := Get_Model_Trace_Label
        (E, False, Append_To_Name);

      E_Type : constant Type_Kind_Id := Retysp (Etype (E));
      --  Taking the full_view of the type to be able to match private
      --  type in the same way as other types because the current intended
      --  behavior is to print private types as if they were public.

   begin
      if not Entity_Comes_From_Source (E) then
         Labels := Symbol_Sets.Empty_Set;

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

               if Get_Type_Kind (Type_Of_Node (Etype (E))) = EW_Abstract
                 or else Is_Mutable_In_Why (E)
               then
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
               | Access_Kind
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

   procedure Add_To_Graph
     (Map      : in out Why_Node_Graphs.Map;
      From, To : Why_Node_Id)
   is
      Position : Why_Node_Graphs.Cursor;
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
              elsif Typ = EW_BitVector_128_Type then Uint_128
              elsif Typ = EW_BitVector_256_Type then UI_From_Int (256)
              else raise Program_Error);
   end BitVector_Type_Size;

   -------------------------
   -- Build_Printing_Plan --
   -------------------------

   function Build_Printing_Plan return Why_Node_Lists.List is
      Seen : Symbol_Set;
      Plan : Why_Node_Lists.List;

      procedure Recurse (Th : W_Theory_Declaration_Id);

      -------------
      -- Recurse --
      -------------

      procedure Recurse (Th : W_Theory_Declaration_Id)
      is
         N : constant Symbol := Get_Name (Th);
      begin
         if Seen.Contains (N) then
            return;
         end if;
         Seen.Insert (N);
         for Incl of Get_List (+Get_Includes (Th)) loop
            declare
               M : constant W_Module_Id :=
                 Get_Module (W_Include_Declaration_Id (Incl));
            begin
               if Get_File (M) = No_Symbol then
                  Recurse (Find_Decl (Get_Name (M)));
               end if;
            end;
         end loop;
         Plan.Append (+Th);
      end Recurse;

   --  Start of processing for Build_Printing_Plan

   begin
      for Th of Why_Sections (WF_Main) loop
         Recurse (+Th);
      end loop;
      return Plan;
   end Build_Printing_Plan;

   ------------------------
   -- Collect_Attr_Parts --
   ------------------------

   procedure Collect_Attr_Parts
     (N         :        Node_Id;
      Attr_Name :        Name_Id;
      Parts     : in out Node_Sets.Set)
   is
      function Old_Attribute (N : Node_Id) return Atree.Traverse_Result;
      --  Search for 'Old attibute and enter its prefix in the map

      function Loop_Entry_Attribute (N : Node_Id) return Atree.Traverse_Result;
      --  Search for 'Loop_Entry attibute and enter its prefix in the map

      --  Local variables

      Loop_Name : E_Loop_Id;

      -------------------
      -- Old_Attribute --
      -------------------

      function Old_Attribute (N : Node_Id) return Atree.Traverse_Result is
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Attribute_Name (N) = Snames.Name_Old
         then
            Parts.Include (Prefix (N));
            --  Attributes are assumed not to be nested in prefixes
            return Atree.Skip;
         else
            return Atree.OK;
         end if;
      end Old_Attribute;

      --------------------------
      -- Loop_Entry_Attribute --
      --------------------------

      function Loop_Entry_Attribute (N : Node_Id) return Atree.Traverse_Result
      is
         Loop_Entry_Name : E_Loop_Id;
      begin
         if Nkind (N) = N_Attribute_Reference
           and then Attribute_Name (N) = Snames.Name_Loop_Entry
         then
            Loop_Entry_Name := Name_For_Loop_Entry (N);

            if Loop_Entry_Name = Loop_Name then
               Parts.Include (Prefix (N));
               --  Attributes are assumed not to be nested in prefixes
               return Atree.Skip;

            end if;
         end if;
         return Atree.OK;
      end Loop_Entry_Attribute;

      procedure Search_Old_Attributes is new Traverse_More_Proc
        (Old_Attribute);

      procedure Search_Loop_Entry_Attributes is new Traverse_More_Proc
        (Loop_Entry_Attribute);

   begin
      if Attr_Name = Snames.Name_Old then
         --  'Old
         Search_Old_Attributes (N);
      else
         --  'Loop_Entry
         Loop_Name := Entity (Identifier (N));
         Search_Loop_Entry_Attributes (N);
      end if;
   end Collect_Attr_Parts;

   procedure Collect_Attr_Parts
     (L         :        Node_Lists.List;
      Attr_Name :        Name_Id;
      Parts     : in out Node_Sets.Set)
   is
   begin
      for N of L loop
         Collect_Attr_Parts (N, Attr_Name, Parts);
      end loop;
   end Collect_Attr_Parts;

   ------------------------------
   -- Collect_Contextual_Nodes --
   ------------------------------

   function Collect_Contextual_Nodes (N : Node_Id) return Node_Sets.Set is
      Contextual_Nodes : Node_Sets.Set;
      Local_Entities   : Node_Sets.Set;

      function Is_Contextual_Part (N : Node_Id) return Atree.Traverse_Result;
      --  Search for contextual node and enter them in the set

      ------------------------
      -- Is_Contextual_Part --
      ------------------------

      function Is_Contextual_Part (N : Node_Id) return Atree.Traverse_Result is
      begin
         --  'Old and Loop_Entry attributes are translated using local
         --  constants introduced at the beginning of the subprogram/loop.
         --  Target name is a local constant declared just before the
         --  assignment.

         if (Nkind (N) = N_Attribute_Reference
             and then Attribute_Name (N) in Name_Old | Name_Loop_Entry)
           or else Nkind (N) = N_Target_Name
         then
            Contextual_Nodes.Insert (N);
            return Atree.Skip;

         --  Constants declared in declare expressions are translated using
         --  local constants.

         elsif Nkind (N) in N_Expanded_Name | N_Identifier then
            if Present (Entity (N))
              and then Comes_From_Declare_Expr (Entity (N))
            then
               Contextual_Nodes.Include (Entity (N));
            end if;
            return Atree.Skip;

         --  Store entities declared in declare expressions local to N in
         --  Local_Entities so that they can be removed from the set of
         --  contextual nodes.

         elsif Nkind (N) = N_Expression_With_Actions then
            declare
               Action : Node_Id := First (Actions (N));
            begin
               while Present (Action) loop
                  case Nkind (Action) is
                     when N_Object_Declaration =>
                        Local_Entities.Include (Defining_Identifier (Action));
                     when others => null;
                  end case;
                  Next (Action);
               end loop;
            end;
            return Atree.OK;
         else
            return Atree.OK;
         end if;
      end Is_Contextual_Part;

      procedure Search_Contextual_Parts is new Traverse_More_Proc
        (Is_Contextual_Part);
   begin
      Search_Contextual_Parts (N);
      Contextual_Nodes.Difference (Local_Entities);
      return Contextual_Nodes;
   end Collect_Contextual_Nodes;

   -----------------------
   -- Collect_Old_Parts --
   -----------------------

   procedure Collect_Old_Parts (N : Node_Id; Parts : in out Node_Sets.Set) is
   begin
      Collect_Attr_Parts (N, Snames.Name_Old, Parts);
   end Collect_Old_Parts;

   procedure Collect_Old_Parts
     (L     :        Node_Lists.List;
      Parts : in out Node_Sets.Set) is
   begin
      Collect_Attr_Parts (L, Snames.Name_Old, Parts);
   end Collect_Old_Parts;

   ------------------
   -- Compute_Spec --
   ------------------

   function Compute_Spec
     (Params : Transformation_Params;
      Nodes  : Node_Lists.List;
      Domain : EW_Domain)
      return W_Expr_Id
   is
      Cur_Spec     : W_Expr_Id;
      Local_Params : Transformation_Params := Params;
   begin

      --  For specs we usually want the pretty-printing markers. This flag is a
      --  no-op for Domains other than EW_Pred.

      if Local_Params.Gen_Marker = GM_None then
         Local_Params.Gen_Marker := GM_Toplevel;
      end if;
      if Nodes.Is_Empty then
         return Bool_True (Domain);
      end if;

      Cur_Spec := Why_Empty;

      for Node of Nodes loop
         declare
            Why_Expr : constant W_Expr_Id :=
              Transform_Expr (Node, EW_Bool_Type, Domain, Local_Params);
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
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain)
      return W_Expr_Id
   is
      Nodes : constant Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide => False, Inherited => False);
   begin
      return Compute_Spec (Params, Nodes, Domain);
   end Compute_Spec;

   -------------------------
   -- Count_Discriminants --
   -------------------------

   function Count_Discriminants (E : Type_Kind_Id) return Natural is
   begin
      if not Has_Discriminants (E) then
         return 0;
      end if;

      declare
         Discr : Opt_E_Discriminant_Id := First_Discriminant (E);
         Count : Natural := 0;
      begin
         while Present (Discr) loop
            Count := Count + 1;
            Next_Discriminant (Discr);
         end loop;

         return Count;
      end;
   end Count_Discriminants;

   ------------------------------
   -- Count_Why_Regular_Fields --
   ------------------------------

   function Count_Why_Regular_Fields (E : Type_Kind_Id) return Natural is
      Count : Natural;

   begin
      --  Add one field for tagged types to represent the unknown extension
      --  components. The field for the tag itself is stored directly in the
      --  Why3 record.

      Count := Natural (Get_Component_Set (E).Length);
      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Regular_Fields;

   --------------------------------
   -- Count_Why_Top_Level_Fields --
   --------------------------------

   function Count_Why_Top_Level_Fields (E : Type_Kind_Id) return Natural is
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

      --  Directly store the __tag field in the record, as this field cannot be
      --  modified after object creation.

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      --  For private types annotated with ownership, we need a is_moved field

      if Has_Ownership_Annotation (E) and then Needs_Reclamation (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Top_Level_Fields;

   -------------------------
   -- Create_Zero_Binding --
   -------------------------

   function Create_Zero_Binding
     (Vars : Why_Node_Lists.List;
      Prog : W_Prog_Id)
      return W_Prog_Id
   is
      Result : W_Prog_Id := Prog;
   begin
      for V of Vars loop
         Result :=
           New_Binding_Ref (Name    => W_Identifier_Id (V),
                            Def     =>
                              New_Discrete_Constant (Value => Uint_0,
                                                     Typ   => Get_Type (+V)),
                            Context => Result,
                            Typ     => Get_Type (+Prog));
      end loop;
      return Result;
   end Create_Zero_Binding;

   -----------------------------------
   -- Get_Dispatching_Call_Contract --
   -----------------------------------

   function Get_Dispatching_Call_Contract
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain)
      return W_Expr_Id
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
      E      : Callable_Kind_Id;
      Kind   : Pragma_Id)
      return W_Pred_Id is
   begin
      return +Get_Dispatching_Call_Contract (Params, E, Kind, EW_Pred);
   end Get_Dispatching_Call_Contract;

   ----------------------
   -- Get_LSP_Contract --
   ----------------------

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Kind   : Pragma_Id)
      return W_Pred_Id
   is
      Conjuncts_List : Node_Lists.List :=
        Find_Contracts (E, Kind, Classwide => True);
   begin
      if Conjuncts_List.Is_Empty then
         Conjuncts_List := Find_Contracts (E, Kind, Inherited => True);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, EW_Pred);
   end Get_LSP_Contract;

   -----------------------
   -- Get_Graph_Closure --
   -----------------------

   function Get_Graph_Closure
     (Map    : Why_Node_Graphs.Map;
      From   : Why_Node_Sets.Set;
      Filter : Why_Node_Sets.Set := Why_Node_Sets.Empty)
      return Why_Node_Sets.Set
   is
      use Why_Node_Sets;
      Result   : Set;
      Work_Set : Set;
      Cur_Node : Why_Node_Id;
      Cur_Ptr  : Why_Node_Graphs.Cursor;

      Ignored  : Why_Node_Sets.Cursor;
      Inserted : Boolean;

   begin
      Work_Set := From;
      Result := From;

      while not Work_Set.Is_Empty loop
         Cur_Node := Work_Set.First_Element;

         Cur_Ptr := Map.Find (Cur_Node);

         if Why_Node_Graphs.Has_Element (Cur_Ptr) then
            for N of Map (Cur_Ptr) loop
               if not Filter.Contains (N) then
                  Result.Insert (New_Item => N,
                                 Position => Ignored,
                                 Inserted => Inserted);

                  if Inserted then
                     Work_Set.Include (N);
                  end if;
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
      Append          : String := "")
      return Symbol_Sets.Set
   is
      S : Symbol_Sets.Set :=
       (Symbol_Sets.To_Set
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

   function Get_Model_Trace_Label (Name : String) return Symbol_Sets.Set is
     (Symbol_Sets.To_Set (NID (Model_Trace_Label & Name)));

   ------------------------------
   -- Get_Static_Call_Contract --
   ------------------------------

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Callable_Kind_Id;
      Kind   : Pragma_Id)
      return W_Pred_Id
   is
      Conjuncts_List : constant Node_Lists.List := Find_Contracts (E, Kind);
   begin
      if Conjuncts_List.Is_Empty then
         return Get_LSP_Contract (Params, E, Kind);
      end if;

      return +Compute_Spec (Params, Conjuncts_List, EW_Pred);
   end Get_Static_Call_Contract;

   --------------------
   -- Has_Post_Axiom --
   --------------------

   function Has_Post_Axiom (E : Callable_Kind_Id) return Boolean is
     (Ekind (E) not in E_Procedure | Entry_Kind
      and then not Has_Pragma_Volatile_Function (E)
      and then not
        Flow_Generated_Globals.Phase_2.Is_Potentially_Nonreturning (E));
   --  Do not generate an axiom for the postcondition of:
   --    * procedures or entries,
   --    * potentially non-returning functions as the axiom could be unsound,
   --    * volatile functions and protected subprograms.

   -----------------------
   -- Init_Why_Sections --
   -----------------------

   procedure Init_Why_Sections is
   begin
      for Kind in W_Section_Id loop
         Make_Empty_Why_Section (Section => Why_Sections (Kind));
      end loop;
   end Init_Why_Sections;

   -----------------
   -- Insert_Item --
   -----------------

   procedure Insert_Item (E : Entity_Id; I : Item_Type) is
   begin
      Ada_Ent_To_Why.Insert (Symbol_Table, E, I);
   end Insert_Item;

   --------------------------------
   -- Insert_Tmp_Item_For_Entity --
   --------------------------------

   procedure Insert_Tmp_Item_For_Entity
     (E       : Entity_Id;
      Name    : W_Identifier_Id;
      Mutable : Boolean := False)
   is
   begin
      Ada_Ent_To_Why.Insert (Symbol_Table, E,
                             Mk_Tmp_Item_Of_Entity (E, Name, Mutable));
   end Insert_Tmp_Item_For_Entity;

   ----------------------------
   -- Is_Initialized_At_Decl --
   ----------------------------

   function Is_Initialized_At_Decl (Obj : Object_Kind_Id) return Boolean is
   begin
      return Is_Constant_Object (Obj)
        or else Present (Expression (Enclosing_Declaration (Obj)));
   end Is_Initialized_At_Decl;

   -----------------------------
   -- Is_Initialized_In_Scope --
   -----------------------------

   function Is_Initialized_In_Scope
     (Obj   : Entity_Id;
      Scope : Unit_Kind_Id)
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
         elsif Obj_Has_Relaxed_Init (Obj) then
            return False;
         else
            declare
               use Flow_Types;

               Read_Ids  : Flow_Id_Sets.Set;
               Write_Ids : Flow_Id_Sets.Set;

            begin
               Flow_Utility.Get_Proof_Globals (Subprogram      => Scope,
                                               Reads           => Read_Ids,
                                               Writes          => Write_Ids,
                                               Erase_Constants => False);

               return Read_Ids.Contains (Direct_Mapping_Id (Obj));
            end;
         end if;

      --  Every global variable referenced inside a package elaboration must be
      --  initialized. In the same way, tasks can only access synchronized or
      --  Part_Of objects, which are always initialized.

      when E_Package | E_Task_Type =>
         return not Obj_Has_Relaxed_Init (Obj);

      when others =>
         raise Program_Error;
      end case;
   end Is_Initialized_In_Scope;

   -----------------------
   -- Is_Mutable_In_Why --
   -----------------------

   function Is_Mutable_In_Why (E : Entity_Id) return Boolean is
   begin
      --  An object is translated as mutable in Why due to being read/write in
      --  SPARK/Ada or due to its represententation in Why.

      case Ekind (E) is
         when E_Loop_Parameter =>

            --  A loop parameter of an genuine loop (but not of a quantified
            --  expression) is mutable.

            return not Is_Quantified_Loop_Param (E);

         when E_Variable =>

            --  Same for variables that are Part_Ofs protected objects; they
            --  are like components for proof.

            return not Is_Quantified_Loop_Param (E)
              and then not Is_Part_Of_Protected_Object (E);

         when E_Task_Type =>

            --  Tasks are modeled as constants

            return False;

         when E_Component | E_Discriminant =>

            --  A component or discriminant is not separately considered
            --  as mutable, only the enclosing object is. This ensures that
            --  components used in the named notation of aggregates are
            --  not considered as references to mutable variables (e.g.
            --  in Expression_Depends_On_Variables).

            return False;

         when E_In_Out_Parameter | E_Out_Parameter | E_Protected_Type =>
            return True;

         when E_Constant =>

            --  Volatile constants with async writers are mutable

            if Has_Volatile (E)
              and then Has_Volatile_Property (E, Pragma_Async_Writers)
            then
               return True;

            --  Constants defined locally to a loop inside a subprogram (or
            --  any other dynamic scope) may end up having different values, so
            --  should be mutable in Why, except when they are defined inside
            --  "actions" (in which case they are defined as local "let" bound
            --  variables in Why) or when they have no variable inputs.

            elsif SPARK_Definition.Is_Loop_Entity (E)
              and then not SPARK_Definition.Is_Actions_Entity (E)
            then
               return Flow_Utility.Has_Variable_Input (E);

            --  An owning access type provides a read/write access to its
            --  designated object.

            else
               return not Is_Constant_In_SPARK (E);
            end if;

         when E_In_Parameter =>

            --  Volatile in parameters with async writers are mutable

            if Has_Volatile (E)
              and then Has_Volatile_Property (E, Pragma_Async_Writers)
            then
               return True;

            --  An owning access type provides a read/write access to procedure
            --  and entry parameters.

            else
               return not Is_Constant_In_SPARK (E)
                 and then
                 not Is_Function_Or_Function_Type (Enclosing_Unit (E));
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Is_Mutable_In_Why;

   -----------------------------
   -- Is_Private_Intrinsic_Op --
   -----------------------------

   function Is_Private_Intrinsic_Op (N : N_Op_Id) return Boolean
   is (Ekind (Entity (N)) = E_Function
       and then Full_View_Not_In_SPARK (Etype (Right_Opnd (N)))
       and then (if Nkind (N) in N_Binary_Op then
                    Full_View_Not_In_SPARK (Etype (Left_Opnd (N)))));

   ----------------------------
   -- Is_Simple_Private_Type --
   ----------------------------

   function Is_Simple_Private_Type (E : Type_Kind_Id) return Boolean is
      Ty : constant Type_Kind_Id := Retysp (E);
   begin
      return Is_Incomplete_Or_Private_Type (Ty)
        and then not Has_Discriminants (Ty)
        and then not Is_Tagged_Type (Ty)
        and then (not Has_Ownership_Annotation (Ty)
                  or else not Needs_Reclamation (Ty));
   end Is_Simple_Private_Type;

   --------------------------
   -- Is_Range_Type_In_Why --
   --------------------------

   function Is_Range_Type_In_Why (T : Type_Kind_Id) return Boolean is
      Ty : constant Type_Kind_Id := Retysp (T);
   begin
      return Is_Signed_Integer_Type (Ty)
        and then not Type_Is_Modeled_As_Base (Ty);
   end Is_Range_Type_In_Why;

   ----------------------------
   -- Make_Empty_Why_Section --
   ----------------------------

   procedure Make_Empty_Why_Section (Section : out Why_Section) is
   begin
      Section := Why_Node_Lists.Empty_List;
   end Make_Empty_Why_Section;

   ------------------------
   -- Map_For_Loop_Entry --
   ------------------------

   function Map_For_Loop_Entry (Loop_Id : Node_Id) return Ada_To_Why_Ident.Map
   is
      use Loop_Entry_Nodes;
      C : constant Loop_Entry_Nodes.Cursor := Loop_Entry_Map.Find (Loop_Id);
   begin
      return (if Has_Element (C) then
                 Element (C)
              else
                 Ada_To_Why_Ident.Empty_Map);
   end Map_For_Loop_Entry;

   -------------------------
   -- Name_For_Loop_Entry --
   -------------------------

   function Name_For_Loop_Entry
     (Attr : N_Attribute_Reference_Id)
      return E_Loop_Id
   is
      function Is_Loop_Stmt (N : Node_Id) return Boolean is
        (Nkind (N) = N_Loop_Statement);

      function Enclosing_Loop_Stmt is new
        First_Parent_With_Property (Is_Loop_Stmt);

      --  Local variables

      Arg       : constant Opt_N_Identifier_Id := First (Expressions (Attr));
      Loop_Id   : E_Loop_Id;
      Loop_Stmt : Node_Id;

   begin
      --  The loop to which attribute Loop_Entry applies is either
      --  identified explicitly in argument, or, if Loop_Entry takes
      --  no arguments, it is the innermost enclosing loop.
      if Present (Arg) then
         Loop_Id := Entity (Arg);

      --  Climb the parent chain to find the nearest enclosing loop
      else
         Loop_Stmt := Enclosing_Loop_Stmt (Attr);
         Loop_Id := Entity (Identifier (Loop_Stmt));
      end if;

      return Loop_Id;
   end Name_For_Loop_Entry;

   function Name_For_Loop_Entry
     (Attr : N_Attribute_Reference_Id)
      return W_Identifier_Id
   is
      Loop_Id : constant E_Loop_Id := Name_For_Loop_Entry (Attr);
   begin
      return Name_For_Loop_Entry (Prefix (Attr), Loop_Id);
   end Name_For_Loop_Entry;

   function Name_For_Loop_Entry
     (Expr    : Node_Or_Entity_Id;
      Loop_Id : E_Loop_Id)
      return W_Identifier_Id
   is
      Result : W_Identifier_Id;

      procedure Get_Name
        (Loop_Id  :        Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map);
      --  Update the mapping Loop_Map with an entry for Expr if not already
      --  present, and store the corresponding identifier in Result.

      --------------
      -- Get_Name --
      --------------

      procedure Get_Name
        (Loop_Id  :        Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map)
      is
         Typ : W_Type_Id;
         Nd  : Node_Id;

         Pos   : Ada_To_Why_Ident.Cursor := Loop_Map.Find (Expr);
         Dummy : Boolean;

         use Ada_To_Why_Ident;

         Attrs : Common_Containers.String_Sets.Set :=
                   Common_Containers.String_Sets.Empty_Set;
         Model_Trace : constant String :=
           --  Here we exclude Loop_Entry expressions and only consider
           --  Entities
           (if Nkind (Expr) in N_Has_Entity then
               "model_trace:" &
               Trim (Source => Entity (Expr)'Image,
                     Side   => Ada.Strings.Left) &
              "'Loop_Entry"
            else "");

      begin
         pragma Unreferenced (Loop_Id);

         if not Has_Element (Pos) then

            if Nkind (Expr) in N_Defining_Identifier then
               Typ := Why_Type_Of_Entity (Expr);
               Nd  := Expr;
            elsif Nkind (Expr) in N_Identifier | N_Expanded_Name then
               Typ := Why_Type_Of_Entity (Entity (Expr));
               Nd  := Entity (Expr);
            else
               Typ := Type_Of_Node (Expr);
               Nd  := Types.Empty;
            end if;

            if Model_Trace /= "" then
               Common_Containers.String_Sets.Insert (Attrs, Model_Trace);
            end if;
            Loop_Map.Insert (Key      => Expr,
                             New_Item => New_Generated_Identifier
                                           (Typ       => Typ,
                                            Ada_Node  => Nd,
                                            Base_Name => "loop_entry",
                                            Attrs     => Attrs),
                             Position => Pos,
                             Inserted => Dummy);
         end if;

         Result := Loop_Map (Pos);
      end Get_Name;

      Cur   : Loop_Entry_Nodes.Cursor;
      Dummy : Boolean;

   --  Start of processing for Name_For_Loop_Entry

   begin
      Loop_Entry_Map.Insert
        (Key      => Loop_Id,
         Position => Cur,
         Inserted => Dummy);

      Loop_Entry_Map.Update_Element
        (Position => Cur,
         Process  => Get_Name'Access);

      return Result;
   end Name_For_Loop_Entry;

   ------------------
   -- Name_For_Old --
   ------------------

   function Name_For_Old (N : Node_Id) return W_Identifier_Id is
      Position : Ada_To_Why_Ident.Cursor;
      Inserted : Boolean;

      use Ada_To_Why_Ident;

   begin
      --  Tentatively insert an empty node to update it later
      Old_Map.Insert (Key      => N,
                      New_Item => Why_Empty,
                      Position => Position,
                      Inserted => Inserted);

      if Inserted then
         declare
            function Is_Contract_Case (P : Node_Id) return Boolean is
              (Is_Pragma (P, Pragma_Contract_Cases));

            function Enclosing_Contract_Case is new
              First_Parent_With_Property (Is_Contract_Case);

            Typ : W_Type_Id;
            Nd  : Node_Id;
            Attrs : Common_Containers.String_Sets.Set :=
                   Common_Containers.String_Sets.Empty_Set;
            Model_Trace : constant String :=
              --  Here we exclude Old expressions and only consider Entities
              (if Nkind (N) in N_Has_Entity then
                  "model_trace:" &
                  Trim (Source => Entity (N)'Image,
                        Side   => Ada.Strings.Left) &
                 "'Old"
               else "");
         begin
            if Nkind (N) in N_Identifier | N_Expanded_Name then
               Typ := Type_Of_Node (N);
               Nd  := Entity (N);
            else
               Typ := Type_Of_Node (Etype (N));
               Nd  := Types.Empty;
            end if;

            if Present (Enclosing_Contract_Case (N)) and then
              Model_Trace /= ""
            then
               Common_Containers.String_Sets.Insert (Attrs, Model_Trace);
               Old_Map (Position) :=
                 New_Generated_Identifier
                   (Base_Name => "old",
                    Typ       => Typ,
                    Ada_Node  => Nd,
                    Attrs     => Attrs);
            else
               Old_Map (Position) :=
                 New_Temp_Identifier (Base_Name => "old",
                                      Typ       => Typ,
                                      Ada_Node  => Nd);
            end if;
         end;
      end if;

      return Old_Map (Position);
   end Name_For_Old;

   -----------------------------
   -- Needs_DIC_Check_At_Decl --
   -----------------------------

   function Needs_DIC_Check_At_Decl (Ty : Type_Kind_Id) return Boolean is
      E : constant Type_Kind_Id := Retysp (Ty);
   begin
      return May_Need_DIC_Checking (E)

        --  We do not want to emit DIC checks for types whose full view is not
        --  in SPARK. If the Restysp is not a private type, then the full view
        --  is necessarily in SPARK.
        --  Otherwise, look at the Retysp and see if it is associated to a
        --  private declaration. In that case, the completion must not be in
        --  SPARK.

        and then
          (not Is_Incomplete_Or_Private_Type (E)
           or else
           Nkind (Enclosing_Declaration (E)) not in
             N_Private_Type_Declaration | N_Private_Extension_Declaration)
        and then Check_DIC_At_Declaration (E);
   end Needs_DIC_Check_At_Decl;

   ----------------------------
   -- Needs_DIC_Check_At_Use --
   ----------------------------

   function Needs_DIC_Check_At_Use (Ty : Type_Kind_Id) return Boolean is
     (May_Need_DIC_Checking (Ty)
       and then not Check_DIC_At_Declaration (Ty));

   --------------------
   -- New_Check_Info --
   --------------------

   function New_Check_Info
     (Range_Check_Ty : Opt_Type_Kind_Id := Empty;
      Divisor        : Node_Or_Entity_Id := Empty) return Check_Info_Type
   is ((Fix_Info     => (Range_Check_Ty => Range_Check_Ty,
                         Divisor        => Divisor),
        Continuation => Continuation_Stack));

   --------------------------------
   -- Nth_Index_Rep_Type_No_Bool --
   --------------------------------

   function Nth_Index_Rep_Type_No_Bool
     (E   : Array_Kind_Id;
      Dim : Positive)
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

   function Type_Is_Modeled_As_Base (T : Type_Kind_Id) return Boolean is
   begin
      return Is_Scalar_Type (T)
        and then (not Has_OK_Static_Scalar_Subtype (T)
                  or else Is_Null_Range (T));
   end Type_Is_Modeled_As_Base;

   ----------------------------------
   -- Type_Needs_Dynamic_Invariant --
   ----------------------------------

   function Type_Needs_Dynamic_Invariant (T : Type_Kind_Id) return Boolean is

      function Has_Potentially_Inherited_Type_Invariants
        (T : Type_Kind_Id)
         return Boolean;
      --  Return True if T or one of its ancestors has a type invariant

      function Type_Needs_Dynamic_Invariant
        (T         : Type_Kind_Id;
         Top_Level : Boolean)
         return Boolean;
      --  Generation of dynamic invariants is slightly different when called
      --  recursively on component types of arrays or records. Top_Level should
      --  be False in recursive calls.

      Incompl_Access_Seen : Entity_Sets.Set;
      --  Set of all the access to incomplete type seen so far. Used to avoid
      --  looping on recursive data structures.

      -----------------------------------------------
      -- Has_Potentially_Inherited_Type_Invariants --
      -----------------------------------------------

      function Has_Potentially_Inherited_Type_Invariants
        (T : Type_Kind_Id)
         return Boolean
      is
         Current : Type_Kind_Id := T;
         Parent  : Type_Kind_Id;
      begin
         loop
            if Has_Invariants_In_SPARK (Current) then
               return True;
            end if;

            Parent := Retysp (Etype (Current));
            exit when Current = Parent;
            Current := Parent;
         end loop;
         return False;
      end Has_Potentially_Inherited_Type_Invariants;

      ----------------------------------
      -- Type_Needs_Dynamic_Invariant --
      ----------------------------------

      function Type_Needs_Dynamic_Invariant
        (T         : Type_Kind_Id;
         Top_Level : Boolean)
         return Boolean
      is
         Ty_Spec   : constant Type_Kind_Id :=
           (if Is_Class_Wide_Type (T) then Get_Specific_Type_From_Classwide (T)
            else T);
         Ty_Ext    : constant Type_Kind_Id := Retysp (Ty_Spec);

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

           --  For access-to-subprogram types, we know that they abide by
           --  their contracts.

           or else Is_Access_Subprogram_Type (Ty_Ext)

           --  For access types with null exclusion, we know that they are not
           --  null.

           or else (Is_Access_Type (Ty_Ext)
                    and then Can_Never_Be_Null (Ty_Ext))

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
           or else Is_Incomplete_Or_Private_Type (Ty_Ext)
           or else Is_Concurrent_Type (Ty_Ext)
         then
            if Has_Discriminants (Ty_Ext) then
               declare
                  Discr : Opt_E_Discriminant_Id := First_Discriminant (Ty_Ext);
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
         elsif Is_Access_Type (Ty_Ext) then

            --  Access types designating incomplete types can lead to recursive
            --  data structures. If the type has already been encountered, we
            --  know that it does not need a dynamic invariant or it would
            --  have been seen.

            if Designates_Incomplete_Type (Ty_Ext) then
               if Incompl_Access_Seen.Contains (Ty_Ext) then
                  return False;
               else
                  Incompl_Access_Seen.Insert (Ty_Ext);
               end if;
            end if;

            return Type_Needs_Dynamic_Invariant
              (Directly_Designated_Type (Ty_Ext), False);
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

   function Type_Of_Node (N : Node_Id) return Type_Kind_Id is
      T : constant Type_Kind_Id :=
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

      return Retysp (T);
   end Type_Of_Node;

   ----------------------------
   -- Use_Guard_For_Function --
   ----------------------------

   function Use_Guard_For_Function (E : Function_Kind_Id) return Boolean is
   begin
      return Gnat2Why_Args.Proof_Generate_Guards

        --  No axioms are generated for volatile functions

        and then not Has_Pragma_Volatile_Function (E)

        --  No axioms are generated for inlined functions

        and then No (SPARK_Definition.Annotate.Retrieve_Inline_Annotation (E))

        --  Functions from predefined units should be safe

        and then not Is_Ignored_Internal (E)

        --  Same for the SPARK library

        and then not In_SPARK_Library_Unit (E)

        --  E has an explicit or implicit postcondition

        and then (Type_Needs_Dynamic_Invariant (Etype (E))
                  or else Has_Contracts (E, Pragma_Postcondition)
                  or else Present (Get_Pragma (E, Pragma_Contract_Cases)));
   end Use_Guard_For_Function;

   -----------------------------
   -- Use_Split_Form_For_Type --
   -----------------------------

   function Use_Split_Form_For_Type (E : Type_Kind_Id) return Boolean is
   begin
      return Is_Scalar_Type (Retysp (E))
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

   ---------------------------
   -- Why_Type_Is_BitVector --
   ---------------------------

   function Why_Type_Is_BitVector (Typ : W_Type_Id) return Boolean is
   begin
      return Typ in EW_BitVector_8_Type
                  | EW_BitVector_16_Type
                  | EW_BitVector_32_Type
                  | EW_BitVector_64_Type
                  | EW_BitVector_128_Type
                  | EW_BitVector_256_Type;
   end Why_Type_Is_BitVector;

   -----------------------
   -- Why_Type_Is_Fixed --
   -----------------------

   function Why_Type_Is_Fixed (Typ : W_Type_Id) return Boolean is
   begin
      return Get_Type_Kind (Typ) = EW_Builtin
        and then Present (Get_Ada_Node (+Typ))
        and then Is_Fixed_Point_Type (Get_Ada_Node (+Typ));
   end Why_Type_Is_Fixed;

   -----------------------
   -- Why_Type_Is_Float --
   -----------------------

   function Why_Type_Is_Float (Typ : W_Type_Id) return Boolean is
   begin
      return Typ in EW_Float_32_Type | EW_Float_64_Type | EW_Float_80_Type;
   end Why_Type_Is_Float;

   --------------------
   -- W_Pred_Vectors --
   --------------------

   package body W_Pred_Vectors is
      procedure Free is new Ada.Unchecked_Deallocation
        (W_Pred_Array, W_Pred_Array_Acc);

      ------------
      -- Append --
      ------------

      procedure Append (V : in out Vector; Pred : W_Pred_Id) is
      begin
         if V.Content = null then
            V.Content := new W_Pred_Array (1 .. 10);
         elsif V.Content'Last = V.Top then
            declare
               New_Size    : constant Natural := 3 * V.Top / 2;
               New_Content : constant W_Pred_Array_Acc :=
                 new W_Pred_Array (1 .. New_Size);
            begin
               New_Content (1 .. V.Top) := V.Content.all;
               Free (V.Content);
               V.Content := New_Content;
            end;
         end if;
         V.Top := V.Top + 1;
         V.Content (V.Top) := Pred;
      end Append;

      --------------
      -- To_Array --
      --------------

      function To_Array
        (V    : in out Vector;
         Init : EW_Literal := EW_True) return W_Pred_Array
      is
      begin
         if V.Top = 0 then
            Free (V.Content);
            return W_Pred_Array'(1 => New_Literal (Value => Init));
         end if;

         return Res : constant W_Pred_Array := V.Content (1 .. V.Top) do
            Free (V.Content);
            V.Top := 0;
         end return;
      end To_Array;
   end W_Pred_Vectors;

begin
   Update_Keywords (Why3_Keywords);
   --  These are not keywords but should not be produced by gnat2why
   Why3_Keywords.Insert ("bool");
   Why3_Keywords.Insert ("int");
   Why3_Keywords.Insert ("real");
   Why3_Keywords.Insert ("unit");
   Why3_Keywords.Insert ("result");
   Why3_Keywords.Insert ("string");
end Gnat2Why.Util;
