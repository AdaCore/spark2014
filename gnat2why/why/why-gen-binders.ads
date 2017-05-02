------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - B I N D E R S                       --
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

with Atree;                  use Atree;
with Common_Containers;      use Common_Containers;
with Einfo;                  use Einfo;
with Namet;                  use Namet;
with SPARK_Definition;       use SPARK_Definition;
with Types;                  use Types;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Ids;                use Why.Ids;
with Why.Sinfo;              use Why.Sinfo;

pragma Warnings (Off);
--  ??? Why.Types" is directly visible as "Types", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Types"). Maybe we should think of renaming it to
--  "Why.W_Types".
with Why.Types;              use Why.Types;
pragma Warnings (On);

package Why.Gen.Binders is
   --  This package provides operations to build binders in program space
   --  and in logic space.

   type Binder_Type is record
      Ada_Node : Node_Id := Empty;
      B_Name   : W_Identifier_Id;
      B_Ent    : Any_Entity_Name;
      Mutable  : Boolean := False;
   end record;
   --  This record represents a variable binding B_Name of type B_Type. In some
   --  cases, extra information is stored concerning the Ada entity that is
   --  represented by this binder. The Ada_Node may be used for that, or the
   --  B_Ent field if no entity node is available for the entity.

   type Binder_Array is array (Positive range <>) of Binder_Type;

   type Item_Enum is (Regular, UCArray, DRecord, Func, Concurrent_Self);
   --  See the comment of the Item_Type type below to see the meaning of this
   --  enum.

   type Item_Bounds is record
      First : W_Identifier_Id;
      Last  : W_Identifier_Id;
   end record;

   type Array_Bounds is array (1 .. Max_Array_Dimensions) of Item_Bounds;

   type Opt_Binder (Present : Boolean := False) is record
      case Present is
         when True  =>
            Binder : Binder_Type;
         when False => null;
      end case;
   end record;

   type Opt_Id (Present : Boolean := False) is record
      case Present is
         when True  =>
            Id : W_Identifier_Id;
         when False => null;
      end case;
   end record;

   type Item_Type (Kind : Item_Enum := Regular) is record
      Local : Boolean;
      --  True if the names of constant parts of the binder are local objects
      --  in Why3.

      case Kind is
         when Regular | Concurrent_Self =>
            Main      : Binder_Type;
         when UCArray =>
            Content   : Binder_Type;
            Dim       : Positive;
            Bounds    : Array_Bounds;
         when DRecord =>
            Typ       : Entity_Id;
            Fields    : Opt_Binder;
            Discrs    : Opt_Binder;
            Constr    : Opt_Id;
            Tag       : Opt_Id;
         when Func    =>
            For_Logic : Binder_Type;
            For_Prog  : Binder_Type;
      end case;
   end record;
   --  An item is like a generalized binder. It is used to represent the
   --  mapping
   --    Ada object  -> Why variables
   --  which is not always 1 to 1. In the common case where it is 1 to 1, the
   --  Kind "Regular" is used. We have three other cases for now: unconstrained
   --  arrays, where extra objects are created to represent the bounds,
   --  functions where we need different translations when used in programs or
   --  in assertions, and records where we can have up to four objects, a set
   --  of fields, a set of discriminant, a 'Constrained attribute, and a 'Tag
   --  attribute. The 'Concurrent_Self' case corresponds to the "self" object
   --  used in task types, protected subprograms and entries, and can be seen
   --  as as "0 to 1" mapping. See also the general description of protected
   --  types in gnat2why.

   type Item_Array is array (Positive range <>) of Item_Type;

   function Item_Array_Length (Arr        : Item_Array;
      Keep_Local : Boolean := True) return Natural;
   --  Return the number of variables that is introduced by the given
   --  item_array (counting items plus e.g. array bounds).

   function To_Binder_Array (A          : Item_Array;
      Keep_Local : Boolean := True) return Binder_Array;
   --  "Flatten" the Item_Array to a binder_array, transforming e.g. array
   --  bounds to binders.

   function New_Binders
     (Anonymous_Binders : W_Type_Array)
      return Binder_Array;

   function New_Universal_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pred     : W_Pred_Id)
      return W_Pred_Id;

   function New_Existential_Quantif
     (Ada_Node : Node_Id := Empty;
      Binders  : Binder_Array;
      Pred     : W_Pred_Id)
      return W_Pred_Id;

   function New_Call
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Typ      : W_Type_Id := Why_Empty)
      return W_Expr_Id;
   --  Create a call to an operation in the given domain with parameters
   --  taken from Binders. Typically, from:
   --
   --     (x1 : type1) (x2 : type2)
   --
   --  ...it produces:
   --
   --     operation_name (x1, x2)

   --  Top-level entities

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Labels      : Name_Id_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
      return W_Declaration_Id;

   function New_Function_Decl
     (Ada_Node    : Node_Id := Empty;
      Domain      : EW_Domain;
      Name        : W_Identifier_Id;
      Items       : Item_Array;
      Return_Type : W_Type_Id := Why_Empty;
      Labels      : Name_Id_Set;
      Effects     : W_Effects_Id := New_Effects;
      Def         : W_Expr_Id := Why_Empty;
      Pre         : W_Pred_Id := True_Pred;
      Post        : W_Pred_Id := True_Pred)
      return W_Declaration_Id;
   --  Localizes Binders before transforming their variable parts into
   --  function parameters.

   function New_Record_Definition
     (Ada_Node : Node_Id := Empty;
      Name     : W_Name_Id;
      Binders  : Binder_Array)
      return W_Declaration_Id;

   function New_Guarded_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : Name_Id;
      Binders  : Binder_Array;
      Triggers : W_Triggers_OId := Why_Empty;
      Pre      : W_Pred_OId := Why_Empty;
      Def      : W_Pred_Id)
      return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>:
   --    forall x1 ... xn.
   --       pre -> <def>

   function New_Defining_Axiom
     (Ada_Node    : Node_Id := Empty;
      Name        : W_Identifier_Id;
      Binders     : Binder_Array;
      Pre         : W_Pred_OId := Why_Empty;
      Def         : W_Term_Id)
      return W_Declaration_Id;
   --  generate an axiom of the form:
   --
   --   axiom <name>___def:
   --    forall x1 ... xn.
   --       pre -> (<name> (x1 .. xn) = <def>)

   function New_Defining_Bool_Axiom
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Binders  : Binder_Array;
      Pre      : W_Pred_Id := Why_Empty;
      Def      : W_Pred_Id)
      return W_Declaration_Id;
   --  Same as new_defining_axiom, but for functions returning booleans.
   --  (for those, predicates are generated instead of logics).

   function Unit_Param return Binder_Type;
   --  return a dummy binder for a single argument of type unit

   function Concurrent_Self_Binder (Ty : Entity_Id) return Binder_Type
     with Pre => Ekind (Ty) in E_Protected_Type | E_Task_Type;
   --  @param Ty a concurrent type entity
   --  @return a binder type which corresponds to the "self" object of that
   --    concurrent type

   function Mk_Tmp_Item_Of_Entity
     (E       : Entity_Id;
      Id      : W_Identifier_Id;
      Mutable : Boolean) return Item_Type
   is
     ((Regular, Local => True, Main => (Ada_Node => E,
                                        B_Name   => Id,
                                        B_Ent    => Null_Entity_Name,
                                        Mutable  => Mutable)));
   --  @param E entity
   --  @param Id identifier
   --  @param Mutable True iff the item is mutable
   --  @return a temporary item from entity E with identity Id

   function Mk_Item_Of_Entity
     (E           : Entity_Id;
      Local       : Boolean := False;
      In_Fun_Decl : Boolean := False) return Item_Type
     with Post => (if Mk_Item_Of_Entity'Result.Kind = Regular then
                   Present (Mk_Item_Of_Entity'Result.Main.Ada_Node)
                   or else
                     Mk_Item_Of_Entity'Result.Main.B_Ent /= Null_Entity_Name);
   --  Create an Item from an Entity
   --  @param E Ada Entity to be translated into an item.
   --  @param Local do not prefix names.
   --  @param In_Fun_Decl Use the type expected in function declaration for
   --  parameters of subprograms (Do not use Actual_Subtype; use
   --  representation type for scalars...).
   --  @return an Item representing the Entity E.

   function Get_Ada_Node_From_Item (B : Item_Type) return Node_Id;
   --  Get the Ada Node of an item.
   --  @param B item whose Ada node we querry.
   --  @return the ada node that produced the binder. If the node is empty,
   --  then either B is the unit binder or it is a binder for effects only.

   function Get_Why_Type_From_Item (B : Item_Type) return W_Type_Id;
   --  Get the why type of an item.
   --  @param B item whose type we querry.
   --  @return the type of the expression that can be reconstructed from B.

   function Reconstruct_Item
     (E           : Item_Type;
      Ref_Allowed : Boolean := True) return W_Expr_Id;
   --  Create an expression out of an item. It does not havoc the content
   --  of volatile objects.
   --  @param E item to be reconstructed.
   --  @param Ref_Allowed use dereference for variables.
   --  @return an Item representing the Entity E.

   function Get_Binders_From_Variables (Variables : Name_Sets.Set;
                                        Compute   : Boolean := False)
                                        return Item_Array;
   --  From a set of names returned by flow analysis, compute an array of
   --  items representing the variables in Why.
   --  @param Variables a set of names returned by flow analysis
   --  @param Compute Should be True if we want to compute binders missing from
   --  the Symbol_Table.
   --  Should only be put to True if only localized versions of names are used.
   --  @result An array of items used to represent these variables in Why

   function Get_Binders_From_Expression (E       : Node_Id;
                                         Compute : Boolean := False)
                                         return Item_Array;
   --  Compute an array of items representing the variables of E in Why.
   --  @param E Ada node for an expression
   --  @param Compute Should be True if we want to compute binders missing from
   --  the Symbol_Table. Only put it to True when the names are localized.
   --  @result An array of items used to represent these variables in Why

   procedure Localize_Variable_Parts (Binders : in out Item_Array;
      Suffix  : String := "");
   --  Changes variables components of Binders to refer to local names.
   --  @param Binders an array of items.

   procedure Push_Binders_To_Symbol_Table (Binders : Item_Array);
   --  Modifies Symbol_Table to store bindings from Binders.
   --  @param Binders an array of items.

   function Get_Args_From_Binders (Binders     : Binder_Array;
                                   Ref_Allowed : Boolean)
                                   return W_Expr_Array;
   --  @param Binders a set of binders
   --  @param Ref_Allowed whether variables should be dereferenced
   --  @result An array of W_Expr_Ids for Binders

   function Get_Args_From_Variables (Variables : Name_Sets.Set;
                                     Ref_Allowed : Boolean)
                                     return W_Expr_Array;
   --  From a set of names returned by flow analysis, compute an array of
   --  expressions for the values of their variable parts.
   --  @param Variables a set of names returned by flow analysis
   --  @param Ref_Allowed whether variables should be dereferenced
   --  @result An array of W_Expr_Ids used to represent the variable parts
   --  of these variables in Why.

   function Get_Args_From_Expression (E           : Node_Id;
                                      Ref_Allowed : Boolean)
                                      return W_Expr_Array;
   --  Compute an array of expressions representing the value of variable
   --  parts of variables of E.
   --  @param E Ada node for an expression
   --  @param Ref_Allowed whether variables should be dereferenced
   --  @result An array of W_Expr_Ids used to represent the variable parts
   --  of these variables in Why.

end Why.Gen.Binders;
