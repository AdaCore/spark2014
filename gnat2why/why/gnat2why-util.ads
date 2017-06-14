------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - U T I L S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Atree;                 use Atree;
with Common_Containers;     use Common_Containers;
with Einfo;                 use Einfo;
with Gnat2Why.Tables;       use Gnat2Why.Tables;
with Sinfo;                 use Sinfo;
with Snames;                use Snames;
with SPARK_Util;            use SPARK_Util;
with SPARK_Util.Types;      use SPARK_Util.Types;
with Types;                 use Types;
with Uintp;                 use Uintp;
with VC_Kinds;              use VC_Kinds;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Ids;               use Why.Ids;
with Why.Sinfo;             use Why.Sinfo;

package Gnat2Why.Util is

   package Ada_Ent_To_Why is

      --  This package is a map from Ada names to a Why node, possibly with a
      --  type. Ada names can have the form of Entity_Ids or Entity_Names.

      type Map is private;
      type Cursor is private;

      Empty_Map  : constant Map;
      No_Element : constant Cursor;

      procedure Insert (M : in out Map;
                        E : Entity_Id;
                        W : Item_Type);

      procedure Insert (M : in out Map;
                        E : Entity_Name;
                        W : Item_Type);

      function Element (M : Map; E : Entity_Id) return Item_Type;
      function Element (C : Cursor) return Item_Type;

      function Find (M : Map; E : Entity_Id) return Cursor;
      function Find (M : Map; E : Entity_Name) return Cursor;

      function Has_Element (M : Map; E : Entity_Id) return Boolean;
      function Has_Element (C : Cursor) return Boolean;

      procedure Push_Scope (M : in out Map);
      --  Mark that a new scope has begun. See the documentation of
      --  [Pop_Scope].

      procedure Pop_Scope (M : in out Map);
      --  Restore the map into the state it was at the last call to Push_Scope.
      --  Does nothing if Push_Scope was never called.

   private

      --  The implementation is a simple map from Ada entities to Items. In
      --  fact we need two maps, because some of the keys are not Entity_Ids,
      --  but Entity_Names.

      --  To implement scopes, for all modifications to the maps, we register
      --  the inverse action into a stack, which is replayed in reverse order
      --  on "pop". This is called the undo stack.

      --  To support several nested scopes, instead of having a nested data
      --  structure, we insert "boundary" actions in the undo stack, which
      --  stop the undoing at that point.

      package Name_To_Why_Map is new Ada.Containers.Hashed_Maps
        (Key_Type => Entity_Name,
         Element_Type    => Item_Type,
         Hash            => Name_Hash,
         Equivalent_Keys => "=",
         "="             => "=");

      package Ent_To_Why is new Ada.Containers.Hashed_Maps
        (Key_Type        => Node_Id,
         Element_Type    => Item_Type,
         Hash            => Node_Hash,
         Equivalent_Keys => "=",
         "="             => "=");

      type Action_Enum is
        (Insert_Ent, Insert_Name, Remove_Ent, Remove_Name, Boundary);

      type Action (Kind : Action_Enum) is record
         case Kind is
            when Boundary =>
               null;
            when Remove_Ent =>
               Rem_Entity : Entity_Id;
            when Remove_Name =>
               Rem_Name : Entity_Name;
            when Insert_Ent | Insert_Name =>
               Ins_Binder : Item_Type;
               case Kind is
                  when Insert_Ent =>
                     Ins_Entity : Entity_Id;
                  when Insert_Name =>
                     Ins_Name : Entity_Name;
                  when others =>
                     null;
               end case;
         end case;
      end record;

      package Undo_Stacks is new Ada.Containers.Indefinite_Doubly_Linked_Lists
        (Element_Type => Action,
         "="          => "=");

      type Map is record
         Entity_Ids   : Ent_To_Why.Map;
         Entity_Names : Name_To_Why_Map.Map;
         Undo_Stack   : Undo_Stacks.List;
      end record;

      Empty_Map  : constant Map :=
        Map'(Entity_Ids   => Ent_To_Why.Empty_Map,
             Entity_Names => Name_To_Why_Map.Empty_Map,
             Undo_Stack   => Undo_Stacks.Empty_List);

      type Cursor_Kind is (CK_Ent, CK_Str);

      type Cursor is record

         --  This should be a variant record, but then it could not be a
         --  completion of the private type above, so here we have the
         --  invariant that when Kind = CK_Ent, then Ent_Cursor is valid,
         --  otherwise, Name_Cursor is valid.

         Kind        : Cursor_Kind;
         Ent_Cursor  : Ent_To_Why.Cursor;
         Name_Cursor : Name_To_Why_Map.Cursor;
      end record;

      No_Element : constant Cursor :=
        Cursor'(Kind        => CK_Ent,
                Ent_Cursor  => Ent_To_Why.No_Element,
                Name_Cursor => Name_To_Why_Map.No_Element);

   end Ada_Ent_To_Why;

   Symbol_Table : Ada_Ent_To_Why.Map := Ada_Ent_To_Why.Empty_Map;

   function Term_Domain (Domain : EW_Domain) return EW_Domain is
      (case Domain is
          when EW_Pred | EW_Term  => EW_Term,
          when EW_Prog | EW_Pterm => EW_Pterm);
   --  @return the term domain corresponding to the [Domain] parameter

   function Prog_Or_Term_Domain (Domain : EW_Domain) return EW_Domain is
      (case Domain is
          when EW_Pred => EW_Term,
          when others  => Domain);
   --  @return the program or term domain corresponding to the [Domain]
   --     parameter, which means essentially converting predicate to term.

   type W_Section_Id is
     (WF_Pure,
      WF_Variables,
      WF_Context,
      WF_Main);

   type Transformation_Params is record
      File        : W_Section_Id;
      --  Identity of the current Why3 file. If needed, new theories and
      --  modules will be created in this file (e.g. for string literals).
      Phase       : Transformation_Phase;
      --  Current transformation phase, which impacts the way code is
      --  transformed from Ada to Why3.
      Gen_Marker  : Boolean;
      --  Flag that is True when the transformation should include in the
      --  generated Why3 node a special label, to be used to show which part
      --  of a possibly large assertion is not proved.
      Ref_Allowed : Boolean;
      --  Flag that is True if references are allowed
      Old_Allowed : Boolean;
      --  Flag that is True if accesses to 'old' values are allowed
   end record;
   --  Set of parameters for the transformation phase

   type Why_Section is limited
      record
         Kind       : W_Section_Id;
         Theories   : Why_Node_Lists.List;
         Cur_Theory : W_Theory_Declaration_Id;
      end record;
   --  Making this type limited is a way to force by-reference passing
   --  of objects of this type. This is needed because we have aliasing between
   --  parameters of many functions and the global variable Why_Sections below.

   Why_File_Name : String_Access;

   procedure Init_Why_Sections;
   --  Call this procedure to initialize the predefined sections of the Why
   --  file. The Unit node is used to initialize the above Why_File_Name
   --  variable.

   Why_Sections : array (W_Section_Id) of Why_Section;

   Why_File_Suffix : constant String := ".mlw";

   function Usual_Params
     (Phase : Transformation_Phase;
      Kind  : W_Section_Id := WF_Main) return Transformation_Params
   is
     (Transformation_Params'
        (File        => Kind,
         Phase       => Phase,
         Gen_Marker  => False,
         Ref_Allowed => (if Phase = Generate_Logic then False else True),
         Old_Allowed => (if Phase = Generate_Logic then False else True)));
   --  Usual set of transformation parameters for a given phase

   ---------------------------------------------
   -- Usual set of parameters for some phases --
   ---------------------------------------------

   function Body_Params return Transformation_Params is
     (Usual_Params (Generate_VCs_For_Body));

   function Assert_Params return Transformation_Params is
     (Usual_Params (Generate_VCs_For_Assert));

   function Logic_Params
     (Kind : W_Section_Id := WF_Main) return Transformation_Params
   is (Usual_Params (Generate_Logic, Kind));

   --------------
   -- Builders --
   --------------

   function Get_Counterexample_Labels
     (E              : Entity_Id;
      Append_To_Name : String := "") return Name_Id_Sets.Set;
   --  Get labels needed for getting counterexample value for entity E.
   --  Note that if the entity does not come from source, return empty set of
   --  labels - these entitities should not be displayed in counterexample.
   --  @param E the entity for that the counterexample value should be get
   --  @param Append_To_Name the string that will be appended to the name of
   --    the corresponding counterexample element

   function Get_Model_Trace_Label
     (E               : Entity_Id;
      Is_Record_Field : Boolean := False;
      Append : String := "") return Name_Id_Sets.Set;
   --  Gets model trace label for given entity.
   --  Note that if the entity is empty or does not come from source code,
   --  return the label "model_trace:".
   --  @param E the entity for that get the trace label
   --  @param Is_Record true if the entity is record field
   --  @param Append the string that will be appended to the name of the
   --    counterexample element

   function Compute_Spec
     (Params : Transformation_Params;
      Nodes  : Node_Lists.List;
      Domain : EW_Domain) return W_Expr_Id;
   --  Compute a proposition from a (possibly empty) list of conjuncts. Returns
   --  True for the empty list.

   function Compute_Spec
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Kind      : Pragma_Id;
      Domain    : EW_Domain;
      Classwide : Boolean := False;
      Inherited : Boolean := False) return W_Expr_Id
   with Pre => Kind in Pragma_Precondition
                     | Pragma_Postcondition
                     | Pragma_Refined_Post;
   --  Compute the precondition or postcondition of the generated Why function.
   --  Kind specifies which one is computed.

   function Create_Zero_Binding
     (Vars : Why_Node_Lists.List;
      Prog : W_Prog_Id) return W_Prog_Id;
   --  Return a program which binds every variable in Vars to 0 in Prog

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id;

   function Get_LSP_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id;
   --  Returns the precondition or postcondition (depending on Kind) for a
   --  dispatching call.

   function Get_Dispatching_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id;

   function Get_Dispatching_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id;
   --  Returns the precondition or postcondition (depending on Kind) for a
   --  dispatching call.

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id;
      Domain : EW_Domain) return W_Expr_Id;

   function Get_Static_Call_Contract
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Pragma_Id) return W_Pred_Id;
   --  Returns the precondition or postcondition (depending on Kind) for a
   --  static call.

   -------------
   -- Queries --
   -------------

   function Is_Record_Type_In_Why (E : Entity_Id) return Boolean is
     (Is_Type (E)
      and then Retysp_Kind (E) in
          Record_Kind | Private_Kind | Concurrent_Kind);

   function Count_Why_Regular_Fields (E : Entity_Id) return Natural with
     Pre => Is_Record_Type_In_Why (E);
   --  @param E record type or private type whose most underlying type is
   --     a record type. E should be a "Representative Type in SPARK".
   --  @return the number of regular fields in the record representing E into
   --     Why3, which contains:
   --     - One field per component of E visible in SPARK
   --       (use Component_Is_Visible_In_SPARK)
   --     - One field for the private part of E if E is a private type
   --     - One field for the extensions of E if E is tagged
   --     - One field for the private components of E's private ancestors if E
   --       is tagged and has private ancestors (use
   --       Has_Private_Ancestor_Or_Root)
   --     - One field for each part_of variable, if E is a protected type

   function Count_Why_Top_Level_Fields (E : Entity_Id) return Natural with
     Pre => Is_Record_Type_In_Why (E);
   --  @param E record type or private type whose most underlying type is
   --     a record type. E should be a "Representative Type in SPARK".
   --  @return the number of top-level fields in the record representing E into
   --     Why3, which contains:
   --     - A field __split_discrs for discriminants if E has at list one
   --     - A field __split_fields for regular fields if E has at list one
   --       (use Count_Why_Regular_Fields)
   --     - A field attr__constrained if E's discriminants have default values
   --     - A field __tag if E is tagged

   function Is_Simple_Private_Type (E : Entity_Id) return Boolean with
     Pre  => Is_Type (E),
     Post => Is_Simple_Private_Type'Result =
       (Has_Private_Type (E)
        and then Count_Why_Top_Level_Fields (Retysp (E)) = 1
        and then Count_Why_Regular_Fields (Retysp (E)) = 1
        and then Is_Type (Get_Component_Set (E).First_Element));
   --  @param E type.
   --  @return True if E is a private type with only a single private field.

   function Count_Discriminants (E : Entity_Id) return Natural with
     Pre  => Is_Type (E);
   --  @param E type.
   --  @return the number of discriminants visible in the Retysp of E
   --  In the translation to Why, use Count_Discriminants instead of
   --  Has_Discriminant to avoid counting hidden discriminants.

   function Expression_Depends_On_Variables (N : Node_Id) return Boolean;
   --  Returns whether the expression E depends on a variable, either directly,
   --  or through the read effects of a function call. This is used to
   --  decide in which output Why file the axiom for the corresponding
   --  constant (for an initialization expression) or the corresponding
   --  aggregate/slice/string literal should be declared.

   function Is_Initialized
     (Obj   : Entity_Id;
      Scope : Entity_Id)
      return Boolean
   with
     Pre => Ekind (Scope) in E_Entry | E_Function | E_Procedure | E_Package
                           | E_Task_Type
       and then not Is_Declared_In_Unit (Obj, Scope)
       and then Is_Mutable_In_Why (Obj);
   --  Returns True if Obj is always initialized in the scope of Scope
   --  @param Obj the entity of an object global to Scope which is variable in
   --         why.
   --  @param Scope the entity of a package, entry, task, or subprogram.

   function Is_Locally_Defined_In_Loop (N : Node_Id) return Boolean;
   --  Returns True if node N is defined locally to a loop

   function Is_Mutable_In_Why (E : Entity_Id) return Boolean with
     Pre => Nkind (E) in N_Defining_Identifier | N_Defining_Operator_Symbol;
   --  Given an identifier, decide if it denotes a variable that is mutable in
   --  the Why translation.

   function May_Need_DIC_Checking (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);
   --  @param E type entity
   --  @return True iff E is the entity for a declaration that may require
   --     checking the DIC, either because it has its own DIC, or because it
   --     is a tagged type which inherits a DIC which requires rechecking.

   function Needs_DIC_Check_At_Decl (Ty : Entity_Id) return Boolean with
     Pre => Has_DIC (Ty);
   --  @param Ty type entity with a DIC
   --  @return True if Ty is the first in its hierarchy to define a non empty
   --     DIC, if its full view is in SPARK, and if its DIC mentions the
   --     current type instance.

   function Needs_DIC_Check_At_Use (Ty : Entity_Id) return Boolean with
     Pre => Has_DIC (Ty);
   --  @param Ty type entity with a DIC
   --  @return True if Ty has a non empty DIC which does not mention the
   --     current type instance.

   function Type_Needs_Dynamic_Invariant (T : Entity_Id) return Boolean with
     Pre => Is_Type (T);
   --  @param T type entity
   --  @return True if T has a non-trivially True dynamic invariant

   function Type_Is_Modeled_As_Base (T : Entity_Id) return Boolean with
     Pre => Is_Type (T);
   --  Returns True if T is a scalar type that should be translated into Why
   --  as a renaming of its base type. This is currently done for dynamic
   --  discrete types and dynamic types defined inside loops, which should not
   --  be treated as having constants bounds, because translation of the loop
   --  in Why may lead to having two coexisting versions of the type.

   function Use_Guard_For_Function (E : Entity_Id) return Boolean with
     Pre => Ekind (E) = E_Function;
   --  Decide wether we need a guard for the axiom specifying the contract of
   --  a function E.

   function Use_Split_Form_For_Type (E : Entity_Id) return Boolean with
     Pre => Is_Type (E);
   --  Decide whether we should use a split form for expressions of a given
   --  type.
   --  This function should be used on entities denoting a type

   ------------------------------
   -- Symbol table subprograms --
   ------------------------------

   procedure Insert_Entity (E       : Entity_Id;
                            Name    : W_Identifier_Id;
                            Mutable : Boolean := False);

   procedure Insert_Item (E : Entity_Id; I : Item_Type);

   function Why_Type_Of_Entity (E : Entity_Id) return W_Type_Id;
   --  For an object entity in Ada, return the Why type that has been
   --  registered for it in the symbol table.

   function Has_Builtin_Why_Type (E : Entity_Id) return Boolean is
     (Get_Type_Kind (Why_Type_Of_Entity (E)) in EW_Builtin | EW_Split)
   with Pre => Has_Scalar_Type (Etype (E));
   --  For a variable or constant decide whether it has a builtin type in Why3.
   --  Must be called after E has been registered in the symbol table (see
   --  [Insert_Entity] and [Insert_Item]).
   --  @param E variable or constant of scalar type
   --  @return True iff E has a builtin type in Why3

   function Why_Type_Is_Float (Typ : W_Type_Id) return Boolean;
   --  Return wether Typ is a Float type.

   function Why_Type_Is_BitVector (Typ : W_Type_Id) return Boolean;
   --  Return wether Typ is a bitvector type.

   function BitVector_Type_Size (Typ : W_Type_Id) return Uint;
   --  Return the size in bit of bitvector type Typ.
   --  raise an exception if Typ is not a bitvector type

   procedure Add_To_Graph (Map : in out Node_Graphs.Map; From, To : Node_Id);
   --  Add the relation From -> To in the given graph
   --  @param Map a graph
   --  @param From the node from which the relation starts
   --  @param To the node to which the relation goes

   function Get_Graph_Closure
     (Map  : Node_Graphs.Map;
      From : Node_Sets.Set) return Node_Sets.Set;
   --  @param Map the graph
   --  @param From the node to start from
   --  @return the set of nodes reachable from the node From in the graph Map

   function Avoid_Why3_Keyword (S : String) return String;
   --  @param S any string
   --  @return a string which is safe tu use as an identifier in Why3, i.e. is
   --    lowercase and does not correspond to a keyword

   function Short_Name (E : Entity_Id) return String;
   --  @param E any entity
   --  @return the actual name used for that entity in Why3 (as opposed to the
   --    name of the module)

   function Nth_Index_Rep_Type_No_Bool (E : Entity_Id; Dim : Positive)
                                        return W_Type_Id;
   --  @param E an array type entity
   --  @param Dim specifies a dimension
   --  @return The rep type of the index entity which corresponds
   --    to the selected dimension or ew_int_id if it is bool

   function Type_Of_Node (N : Node_Id) return Entity_Id;
   --  @param N any node
   --  @return the type of the node; if N is already a type, return that,
   --    otherwise return the Etype. Also, if the most underlying full view of
   --    a private type is in SPARK, that one is returned instead of the
   --    private type.

   type Range_Check_Kind is
     (RCK_Overflow,
      RCK_FP_Overflow,
      RCK_Range,
      RCK_Length,
      RCK_Index,
      RCK_Range_Not_First,
      RCK_Range_Not_Last,
      RCK_Overflow_Not_First,
      RCK_Overflow_Not_Last);

   function To_VC_Kind (R : Range_Check_Kind) return VC_Kind
   is
     (case R is
         when RCK_Overflow           => VC_Overflow_Check,
         when RCK_FP_Overflow        => VC_FP_Overflow_Check,
         when RCK_Range              => VC_Range_Check,
         when RCK_Length             => VC_Length_Check,
         when RCK_Index              => VC_Index_Check,
         when RCK_Range_Not_First    => VC_Range_Check,
         when RCK_Range_Not_Last     => VC_Range_Check,
         when RCK_Overflow_Not_First => VC_Overflow_Check,
         when RCK_Overflow_Not_Last  => VC_Overflow_Check);
   --  to convert a Range_Check_Kind to a VC_Kind

end Gnat2Why.Util;
