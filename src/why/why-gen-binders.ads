------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

with Common_Containers;    use Common_Containers;
with Flow_Types;           use Flow_Types;
with GNATCOLL.Symbols;     use GNATCOLL.Symbols;
with Snames;               use Snames;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Definition;     use SPARK_Definition;
with SPARK_Util;           use SPARK_Util;
with Types;                use Types;
with VC_Kinds;             use VC_Kinds;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Terms;        use Why.Gen.Terms;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;

pragma Warnings (Off);
--  ??? Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types; use Why.Types;
pragma Warnings (On);

package Why.Gen.Binders is
   --  This package provides operations to build binders in program space
   --  and in logic space.

   type Binder_Type is record
      Ada_Node : Node_Id := Empty;
      B_Name   : W_Identifier_Id;
      B_Ent    : Any_Entity_Name;
      Mutable  : Boolean := False;
      Labels   : Symbol_Sets.Set;
   end record;
   --  This record represents a variable binding B_Name. In some cases, extra
   --  information is stored concerning the Ada entity that is represented by
   --  this binder. The Ada_Node may be used for that, or the B_Ent field if no
   --  entity node is available for the entity. Labels is a set of label
   --  associated to the binder. It is used to provide counterexample labels
   --  to record components inside record declarations.

   type Binder_Array is array (Positive range <>) of Binder_Type;

   type Item_Enum is
     (Regular, UCArray, DRecord, Pointer, Subp, Concurrent_Self);
   --  See the comment of the Item_Type type below to see the meaning of this
   --  enum.

   type Item_Bounds is record
      First : W_Identifier_Id;
      Last  : W_Identifier_Id;
   end record;

   type Array_Bounds is array (1 .. Max_Array_Dimensions) of Item_Bounds;

   type Opt_Binder (Present : Boolean := False) is record
      case Present is
         when True =>
            Binder : Binder_Type;

         when False =>
            null;
      end case;
   end record;

   type Opt_Id (Present : Boolean := False) is record
      case Present is
         when True =>
            Id : W_Identifier_Id;

         when False =>
            null;
      end case;
   end record;

   --  An item is like a generalized binder. It is used to represent the
   --  mapping (Ada object -> Why variables) which is not always 1 to 1.
   type Item_Type (Kind : Item_Enum := Regular) is record
      Local : Boolean;
      --  True if the names of constant parts of the binder are local objects
      --  in Why3.

      Init : Opt_Id;
      --  Optional init flag for scalar objects which have Init_By_Proof

      Is_Moved : Opt_Id;
      --  Optional move tree for objects containing allocated parts

      Valid : Opt_Id;
      --  Optional validity flag for potentially invalid objects

      case Kind is
         --  Common case where mapping from Ada object to Why object is 1 to 1

         when Regular

            --  Case corresponding to the "self" object used in task types,
            --  protected subprograms and entries, which can be seen as "0 to 1"
            --  mapping. See also the general description of protected types in
            --  gnat2why.

            | Concurrent_Self
         =>
            Main : Binder_Type;

            --  Case of unconstrained arrays, where extra objects are created to
            --  represent the bounds.

         when UCArray =>
            Content : Binder_Type;
            Dim     : Positive;
            Bounds  : Array_Bounds;

            --  Case of pointers, with disjoint parts for their value and is_null
            --  components, as well as a Mutable boolean registering whether the
            --  pointer itself is mutable (as opposed to its designated value
            --  only).

         when Pointer =>
            P_Typ   : Entity_Id;
            Value   : Binder_Type;
            Is_Null : W_Identifier_Id;
            Mutable : Boolean;

            --  Case of records where we can have up to four objects, a set of
            --  fields, a set of discriminants, a 'Constrained attribute, and a
            --  'Tag attribute.

         when DRecord =>
            Typ    : Entity_Id;
            Fields : Opt_Binder;
            Discrs : Opt_Binder;
            Constr : Opt_Id;
            Tag    : Opt_Id;

            --  Case of subprograms where we need different translations when used
            --  in programs or in assertions, plus possibly refined and dispatch
            --  versions.

         when Subp =>
            For_Logic      : Opt_Id;
            For_Prog       : W_Identifier_Id;
            Refine_Prog    : Opt_Id;
            Dispatch_Logic : Opt_Id;
            Dispatch_Prog  : Opt_Id;
      end case;
   end record;

   type Item_Array is array (Positive range <>) of Item_Type;

   type Handling is (Erase, Local_Only, Keep);
   --  Defines the the handling that should be applied to parts of a binder.
   --  If it is Erase, they are ignored, Local_Only means that we keep them
   --  only for local binders, and Keep that they should always be included.

   function Item_Array_Length
     (Arr                   : Item_Array;
      Keep_Const            : Handling := Local_Only;
      Ignore_Init_And_Valid : Boolean := False) return Natural;
   --  @param Arr an array of items.
   --  @param Keep_Const handling to be used for constant parts of Arr.
   --  @param Ignore_Init_And_Valid whether top-level initialization and
   --    validity flags should be counted.
   --  @return the number of variables that is introduced by Arr (counting
   --    items plus e.g. array bounds).

   function To_Binder_Array
     (A : Item_Array; Keep_Const : Handling := Local_Only) return Binder_Array
   with
     Post => To_Binder_Array'Result'Length = Item_Array_Length (A, Keep_Const);
   --  "Flatten" the Item_Array to a binder_array, transforming e.g. array
   --  bounds to binders.
   --  @param A an array of items.
   --  @param Keep_Const handling to be used for constant parts of Arr.

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id) return W_Pred_Id;

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Typ      : W_Type_Id := Why_Empty) return W_Expr_Id;
   --  Create a call to an operation in the given domain with parameters
   --  taken from Binders. Typically, from:
   --
   --     (x1 : type1) (x2 : type2)
   --
   --  ...it produces:
   --
   --     operation_name (x1, x2)

   --  Top-level entities

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Typ      : W_Type_Id := Why_Empty) return W_Term_Id
   is (+W_Expr_Id'(New_Call (Ada_Node, EW_Term, Name, Binders, Typ)));

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Location    : Source_Ptr;
      Labels      : Symbol_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred) return W_Declaration_Id;

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Items       : Item_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Location    : Source_Ptr;
      Labels      : Symbol_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred) return W_Declaration_Id;
   --  Localizes Binders before transforming their variable parts into
   --  function parameters.

   function New_Record_Definition
     (Ada_Node : Node_Id := Empty; Name : W_Name_Id; Binders : Binder_Array)
      return W_Declaration_Id;

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : Symbol;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Pred_Id;
      Dep      : W_Axiom_Dep_OId := Why_Empty) return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>:
   --    forall x1 ... xn.
   --       pre -> <def>

   function New_Defining_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Term_Id) return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>___def:
   --    forall x1 ... xn.
   --       pre -> (<name> (x1 .. xn) = <def>)

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Fun_Name : String := "";
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_Id := Why_Empty;
      Def      : W_Pred_Id;
      Dep_Kind : EW_Axiom_Dep_Kind) return W_Declaration_Id;
   --  Same as new_defining_axiom, but for functions returning booleans.
   --  (for those, predicates are generated instead of logics).

   function Unit_Param
     (Prefix : String := ""; Ada_Node : Node_Id := Empty) return Binder_Type;
   --  return a dummy binder for a single argument of type unit

   function Concurrent_Self_Ident (Ty : Entity_Id) return W_Identifier_Id
   with Pre => Ekind (Ty) in E_Protected_Type | E_Task_Type;
   --  @param Ty a concurrent type entity
   --  @return an identifier which corresponds to the "self" object of that
   --    concurrent type

   function Concurrent_Self_Move_Tree_Id
     (Ty : Entity_Id) return W_Identifier_Id
   with Pre => Ekind (Ty) in E_Protected_Type;
   --  @param Ty a concurrent type entity which contains allocated parts
   --  @return an identifier which corresponds to the move tree of the "self"
   --    object of that concurrent type.

   function Concurrent_Self_Binder
     (Ty : Entity_Id; Mutable : Boolean := True) return Binder_Type
   with Pre => Ekind (Ty) in E_Protected_Type | E_Task_Type;
   --  @param Ty a concurrent type entity
   --  @param Mutable Value for the binder Mutable component
   --  @return a binder type which corresponds to the "self" object of that
   --    concurrent type

   function Mk_Tmp_Item_Of_Entity
     (E : Entity_Id; Id : W_Identifier_Id; Mutable : Boolean) return Item_Type
   is ((Regular,
        Local    => Get_Module (Get_Name (Id)) = Why_Empty,
        Init     => <>,
        Is_Moved => <>,
        Valid    => <>,
        Main     =>
          (Ada_Node => E,
           B_Name   => Id,
           B_Ent    => Null_Entity_Name,
           Mutable  => Mutable,
           Labels   => <>)));
   --  @param E entity
   --  @param Id identifier
   --  @param Mutable True iff the item is mutable
   --  @return a temporary item from entity E with identity Id

   function Mk_Item_Of_Entity
     (E           : Entity_Id;
      Local       : Boolean := False;
      In_Fun_Decl : Boolean := False;
      Hide_Info   : Boolean := False) return Item_Type
   with
     Pre  => Entity_In_SPARK (E),
     Post =>
       (if Mk_Item_Of_Entity'Result.Kind = Regular
        then
          Present (Mk_Item_Of_Entity'Result.Main.Ada_Node)
          or else Mk_Item_Of_Entity'Result.Main.B_Ent /= Null_Entity_Name);
   --  Create an Item from an Entity
   --  @param E Ada Entity to be translated into an item.
   --  @param Local do not prefix names.
   --  @param In_Fun_Decl Use the type expected in function declaration for
   --    parameters of subprograms (Do not use Actual_Subtype; use
   --    representation type for scalars...).
   --  @param Hide_Info True if information for E is hidden in the current
   --    scope.
   --  @return an Item representing the Entity E.

   function Get_Ada_Node_From_Item (B : Item_Type) return Node_Id;
   --  Get the Ada Node of an item.
   --  @param B item whose Ada node we query.
   --  @return the Ada node that produced the binder. If the node is empty,
   --    then either B is the unit binder or it is a binder for effects only.

   function Get_Why_Type_From_Item (B : Item_Type) return W_Type_Id;
   --  Get the why type of an item.
   --  @param B item whose type we query.
   --  @return the type of the expression that can be reconstructed from B.

   function Get_Ada_Type_From_Item (B : Item_Type) return Entity_Id;
   --  Get the Ada type of an item.
   --  @param B item whose type we query.
   --  @return the type of the Ada node associated to B.

   function Item_Is_Mutable (B : Item_Type) return Boolean;
   --  Check if an Item is Mutable.
   --  @param B item we query.
   --  @return True if B is mutable

   function Reconstruct_Item
     (E : Item_Type; Ref_Allowed : Boolean := True) return W_Term_Id;
   --  Create an expression out of an item. It does not havoc the content
   --  of volatile objects.
   --  @param E item to be reconstructed.
   --  @param Ref_Allowed use dereference for variables.
   --  @return an Item representing the Entity E.

   function Get_Binders_From_Variables
     (Variables : Flow_Id_Sets.Set; Ignore_Self : Boolean := False)
      return Item_Array
   with
     Pre =>
       (for all V of Variables =>
          V.Kind in Direct_Mapping | Magic_String
          and then V.Variant = Normal_Use);
   --  From a set of names returned by flow analysis, compute an array of
   --  items representing the variables in Why.
   --  @param Variables a set of names returned by flow analysis
   --  @param Ignore_Self True if we want to discard references to protected
   --  components.
   --  Should only be put to True if only localized versions of names are used.
   --  @result An array of items used to represent these variables in Why

   subtype Contextual_Node is Node_Id
   with
     Ghost,
     Predicate =>
       (case Nkind (Contextual_Node) is
          when N_Target_Name => True,
          when N_Attribute_Reference =>
            Attribute_Name (Contextual_Node) in Name_Old | Name_Loop_Entry,
          when N_Defining_Identifier =>
            Comes_From_Declare_Expr (Contextual_Node),
          when others => False);
   --  Nodes whose translation is a local Why3 objects defined in the context
   --  of the expression. This includes attributes 'Loop_entry and 'Old, target
   --  name, and constants coming from declare expressions.

   function Get_Binders_From_Contextual_Nodes
     (Contextual_Nodes : Node_Sets.Set) return Item_Array
   with
     Pre  => (for all E of Contextual_Nodes => E in Contextual_Node),
     Post =>
       (for all Item of Get_Binders_From_Contextual_Nodes'Result =>
          Item.Local and Item.Kind = Regular and not Item.Main.Mutable);
   --  A set of of items for contextual nodes.
   --  NB. For split array types, old items will not contain the bounds of
   --  the array. These elements should be provided separately (it is usually
   --  done by providing the binders for variables referenced in the
   --  expression).

   function Get_Binders_From_Expression (Expr : Node_Id) return Item_Array
   with Pre => Nkind (Expr) in N_Subexpr;
   --  Compute an array of items representing the variables of E in Why.
   --  @param Expr Ada node for an expression
   --  @result An array of items used to represent these variables in Why

   procedure Localize_Binders
     (Binders        : in out Item_Array;
      Suffix         : String := "";
      Only_Variables : Boolean := True);
   --  Changes components of Binders to refer to local names.
   --  @param Binders an array of items.
   --  @param Suffix a string to add as a suffix of local names of Binders.
   --  @param Only_Variables True if we only need local names for variable
   --     parts of Binders.

   function Get_Localized_Binders_From_Variables
     (Variables      : Flow_Id_Sets.Set;
      Ignore_Self    : Boolean := False;
      Suffix         : String := "";
      Only_Variables : Boolean := True) return Item_Array;
   --  From a set of names returned by flow analysis, computes an array of
   --  items representing variables by fresh parameters.
   --  The parameters are those of a call to Get_Binders_From_Variables
   --  followed by Localize_Binders.

   procedure Push_Binders_To_Symbol_Table (Binders : Item_Array);
   --  Modifies Symbol_Table to store bindings from Binders.
   --  @param Binders an array of items.

   function Get_Args_From_Binders
     (Binders : Binder_Array; Ref_Allowed : Boolean) return W_Expr_Array;
   --  @param Binders a set of binders
   --  @param Ref_Allowed whether variables should be dereferenced
   --  @result An array of W_Expr_Ids for Binders

   function Get_Args_From_Variables
     (Variables : Flow_Id_Sets.Set; Ref_Allowed : Boolean) return W_Expr_Array;
   --  From a set of names returned by flow analysis, compute an array of
   --  expressions for the values of their variable parts.
   --  @param Variables variables returned by flow analysis
   --  @param Ref_Allowed whether variables should be dereferenced
   --  @result An array of W_Expr_Ids used to represent the variable parts
   --  of these variables in Why.

   generic
      with
        procedure Effects_Append
          (Id : W_Effects_Id; New_Item : W_Identifier_Id);
   procedure Effects_Append_Binder (Eff : W_Effects_Id; Binder : Item_Type);
   --  Append to effects Eff the variable associated with an item
   --  @param Binder variable to add to Eff

   function Get_Init_Id_From_Object
     (Obj : Entity_Id; Ref_Allowed : Boolean) return W_Expr_Id;
   --  Return the init flag associated to Obj in the Symbol_Table if any.
   --  Otherwise, return Why_Empty.

   function Object_Has_Valid_Id (Obj : Entity_Id) return Boolean;
   --  Return True is Obj has an associated validity flag

   function Get_Valid_Id_From_Item
     (Item : Item_Type; Ref_Allowed : Boolean) return W_Term_Id;
   --  Return the valid flag of Item if any. Otherwise, return Why_Empty.

   function Get_Valid_Id_From_Object
     (Obj : Entity_Id; Ref_Allowed : Boolean) return W_Term_Id;
   --  Return the valid flag associated to Obj in the Symbol_Table if any.
   --  Otherwise, return Why_Empty.

end Why.Gen.Binders;
