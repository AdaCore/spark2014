------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with GNATCOLL.Symbols;     use GNATCOLL.Symbols;
with Gnat2Why.Util;        use Gnat2Why.Util;
with Snames;               use Snames;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Modules;    use Why.Atree.Modules;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Types;            use Why.Types;

package Why.Gen.Arrays is
   --  This package encapsulates the encoding of Ada arrays into Why.
   --
   --  --------------------
   --  Modeling Array Types
   --  --------------------
   --
   --  The operations on array content (access, update, sliding)
   --  are modeled in Why by a "map" type. It maps representative index values
   --  (an "int" or a bitvector per dimension) to values of the component type.
   --  Operations on this type include:
   --    - "get" to access the map at a certain index
   --    - "set" to update the map at a certain index
   --    - "slide" to shift the objects of the map
   --    - "slice" to restrict the map to new bounds
   --
   --  There is also a function to express Ada equality.
   --
   --  See the theories Array__1 to Array__4 in _gnatprove_standard.mlw for
   --  this model.
   --
   --  The Why model of statically constrained array types consists of this
   --  map type, with constants "first" and "last" per dimension for the bounds
   --  of the type. See Constr_Array and Constr_Array_N in ada__model.mlw for
   --  this encoding.
   --
   --  The Why model of unconstrained and dynamically constrained array types
   --  consists of a record containing the map and an "index" object per
   --  dimension. Each index object stores bounds in the closed base type of
   --  the Ada index type. See ada__model.mlw, the theories Unconstr_Array and
   --  Unconstr_Array_N for this encoding. Dynamically constrained types reuse
   --  the representation of their base type; see Array_Type_Is_Clone.
   --
   --  The abstract predicate has_bounds states that map values outside the
   --  given bounds are fixed. The well_formed predicate relates has_bounds to
   --  the bounds of the array representation. It is part of the array's
   --  dynamic invariant and must be maintained by array operations. For the
   --  rationale, see "Representative Array Theories" in the "Translation to
   --  Why3" chapter of the developer guide.
   --
   --  ----------------------
   --  Sharing Array Theories
   --  ----------------------
   --
   --  Representative map theories are shared by arrays with the same
   --  representative index types and the same closed component type. Their
   --  bounds do not affect this sharing. Get_Array_Theory_Name constructs the
   --  module name from these types; M_Arrays in Why.Atree.Modules uses that
   --  name as its key. The optional __init_wrapper suffix distinguishes the
   --  map theory for an array's initialization wrapper.
   --
   --  M_Arrays_1 stores additional symbols for one-dimensional maps, including
   --  concatenation and singleton. Comparison and logical-operator symbols
   --  are stored separately in M_Arrays_1_Comp and M_Arrays_1_Bool_Op.
   --
   --  -------------------------
   --  Modeling Array Operations
   --  -------------------------

   --  Indexing and Assignment
   --  -----------------------
   --
   --  Indexing and component assignment are expressed using the "get" and
   --  "set" operations on the map type. No shifting of the index takes place,
   --  "A (I)" in Ada directly becomes "get <array object> i" in Why. For
   --  statically constrained arrays, no map extraction is needed.
   --
   --  For unconstrained or dynamically constrained arrays, the map must be
   --  extracted from the array record before indexing. Component assignment
   --  uses the Why record update syntax:
   --
   --    { x with elts = set x.elts i v }
   --
   --  Slicing
   --  -------
   --
   --  Slicing preserves elements within the new bounds. The "slice" operation
   --  establishes has_bounds on the resulting map for these bounds. It is a
   --  no-op when the input map already has these bounds. New_Slice_Call
   --  operates on the map; bounds are carried by the surrounding array
   --  representation. Runtime checks are generated separately.
   --
   --  Sliding
   --  -------
   --
   --  Sliding aligns the source elements with the target bounds, for example
   --  when converting to a constrained array type. We use the "slide" function
   --  for that.
   --
   --  Accessing bounds of the type or the object
   --  ------------------------------------------
   --
   --  For statically constrained types, the type declaration comes with the
   --  appropriate constants. Both T'First for such a type T and X'First for
   --  an object X of that type are translated to the same constant.
   --
   --  For unconstrained or dynamically constrained array objects, the bounds
   --  are stored in the object and retrieved with the appropriate selection.
   --
   --  Equality
   --  --------
   --
   --  Predefined equality calls the map's "bool_eq" function with the bounds
   --  of both operands. See "Accessing bounds of the type or the object".
   --
   --  Conversions
   --  -----------
   --
   --  When the source and target representations share a map type, conversions
   --  change how the bounds are supplied and apply sliding if needed.
   --
   --  A conversion from an unconstrained object to a statically constrained
   --  one selects the "elts" field, because the target bounds are provided as
   --  constants. Sliding aligns the elements with those bounds if necessary.
   --  Runtime checks are generated separately.
   --
   --  A conversion between statically constrained objects sharing a map type
   --  is a no-op except for sliding, if necessary.
   --
   --  A conversion from statically constrained objects to an unconstrained
   --  type requires building an unconstrained object with the map as its
   --  "elts" field and the bounds from the constants of the source type.
   --
   --  A conversion between unconstrained objects is similar, but the bounds
   --  are retrieved from the object instead of the type.
   --
   --  If the map types differ, Create_Array_Conversion_Theory_If_Needed emits
   --  a conversion function and its defining axiom. M_Arrays_Conversion caches
   --  these functions by source and target representative theory names.
   --  Get_Array_Conversion_Name retrieves the cached symbol. Corresponding
   --  indexes must have the same representative type.

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive);
   --  Add an argument for the corresponding attribute of the array. See
   --  also [Get_Array_Attr]. Add_Attr_Arg will work with constrained and
   --  unconstrained arrays.

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive;
      Params  : Transformation_Params := Body_Params)
   with
     Pre =>
       (Attr in Attribute_First | Attribute_Last | Attribute_Length
        and then Is_Constrained (Ty))
       or else
         (Attr = Attribute_First
          and then
            Is_Fixed_Lower_Bound_Index_Subtype (Nth_Index_Type (Ty, Dim)));
   --  This variant of Add_Attr_Arg will only work when the attribute of the
   --  type is constrained.

   function Array_From_Split_Form
     (I           : Item_Type;
      Domain      : EW_Domain;
      Ref_Allowed : Boolean := True;
      Alias       : W_Expr_Id := Why_Empty) return W_Expr_Id
   with Pre => I.Kind = UCArray;
   --  Reconstructs a complete array from an item in split form.

   procedure Declare_Ada_Array (Th : Theory_UC; E : Entity_Id);
   --  Introduce all the necessary declarations for an Ada array declaration;
   --  E is the entity which contains the relevant type information (the
   --  underlying type).

   procedure Declare_Init_Wrapper_For_Array (Th : Theory_UC; E : Entity_Id)
   with Pre => Has_Array_Type (E) and then Has_Init_Wrapper (E);
   --  Introduce necessary declarations for the wrapper type for E

   procedure Declare_Additional_Symbols_For_String (Th : Theory_UC);
   --  Declare to_string and of_string functions used for 'Image and 'Value
   --  attributes.

   function New_Array_Access
     (Ada_Node : Node_Id := Empty;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Domain   : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to an array access

   function New_Array_Access
     (Ada_Node : Node_Id := Empty; Ar : W_Term_Id; Index : W_Expr_Array)
      return W_Term_Id
   is (+W_Expr_Id'(New_Array_Access (Ada_Node, +Ar, Index, EW_Term)));

   function Array_Convert_To_Base
     (Domain : EW_Domain; Ar : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Type_Kind (Get_Type (Ar)) = EW_Abstract;
   --  "Ar" must be a Why expression of unconstrained array type. Convert it to
   --  the "split" view of UC arrays

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Ar     : W_Expr_Id;
      First  : W_Expr_Id;
      Last   : W_Expr_Id) return W_Expr_Id;
   --  This variant can be used when we need to build an unconstrained array,
   --  but "Ar" is not in split form. We need to provide the target type and
   --  first/last expressions explicitly.

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Ar     : W_Expr_Id;
      Bounds : W_Expr_Array) return W_Expr_Id;
   --  Variant of the convertion function used to build an unconstrained array
   --  from its split form [Ar] and its [Bounds] expressions

   function Array_Convert_From_Base
     (Domain : EW_Domain; Old_Ar : W_Expr_Id; New_Base : W_Expr_Id)
      return W_Expr_Id
   with Pre => Get_Type_Kind (Get_Type (New_Base)) = EW_Split;
   --  "New_Base" must be a Why expression of unconstrained array type, in
   --  split form. Convert it to the regular unconstrained form, using Old_Ar's
   --  bounds.

   function New_Array_Range_Expr
     (Index_Expr : W_Term_Id;
      Array_Expr : W_Term_Id;
      Domain     : EW_Domain;
      Dim        : Positive) return W_Expr_Id;
   --  Construct an expression stating that an index is in an array's bound.
   --  @param Index_Expr expression for the considered index
   --  @param Array_Expr expression for the array
   --  @param Domain expected domain of the range expression
   --  @param Dim considered index in the array
   --  @param an expression
   --  <array_expr>.first<dim> <= <index_expr> <= <array_expr>.last<dim>

   function New_Array_Update
     (Ada_Node : Node_Id;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Value    : W_Expr_Id;
      Domain   : EW_Domain) return W_Expr_Id;
   --  ???

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id; Right_Arr : W_Term_Id; Dim : Positive)
      return W_Pred_Id;
   --  @param Left_Arr array expression whose bounds should be compared
   --  @param Right_Arr
   --  @param Dim number of dimensions in the arrays
   --  @return a predicate of the form:
   --
   --    <left_arr>.first1 = <right_arr>.first1 /\
   --    <left_arr>.last1 = <right_arr>.last1 /\ ...

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id;
      Right_Ty : Entity_Id;
      Params   : Transformation_Params := Body_Params) return W_Pred_Id
   with Pre => Is_Constrained (Right_Ty);
   --  same as above but takes the bounds of a type for Right

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id; Right_Bounds : W_Expr_Array; Dim : Positive)
      return W_Pred_Id
   with Pre => Right_Bounds'Length = Dim * 2;
   --  same as above but with the bounds stored in an array

   function New_Length_Equality
     (Left_Arr : W_Term_Id; Right_Arr : W_Term_Id; Dim : Positive)
      return W_Pred_Id;
   --  @param Left_Arr array expression whose length should be compared to
   --  @param Right_Arr
   --  @param Dim number of dimensions in the arrays
   --  @return a predicate of the form:
   --
   --    (if <left_arr>.first1 <= <left_arr>.last1 then
   --       <right_arr>.first1 <= <right_arr>.last1
   --       /\ <left_arr>.last1 - <left_arr>.first1 =
   --          <right_arr>.last1 - <right_arr>.first1
   --     else <right_arr>.last1 < <right_arr>.first1) /\ ...

   function New_Length_Equality
     (Left_Arr : W_Term_Id; Right : Entity_Id; Dim : Positive) return W_Pred_Id
   with Pre => Is_Constrained (Right);
   --  Same as above but with a constrained array type

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Args   : W_Expr_Array;
      Params : Transformation_Params := Body_Params) return W_Expr_Id;
   --  @param Domain The domain of the returned expression
   --  @param Ty the entity for the Ada array type
   --  @param Args bound values on which we want to check the dynamic predicate
   --  @param Params transformation parameters
   --  @return a call to the Ty's dynamic property:
   --
   --    <Dynamic_Prop_Name (Ty)>
   --              Nth_Index_Type (Ty, 1)'First Nth_Index_Type (Ty, 1)'Last
   --              Args (1) Args (2) ...

   function New_Element_Equality
     (Ada_Node  : Node_Id := Empty;
      Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Index     : W_Expr_Array) return W_Pred_Id;
   --  Return a predicate of the form:
   --
   --    <left_arr>[<index>] = <right_arr>[<index>]

   function New_Move_Tree_Array_Access
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id
   with
     Pre =>
       Is_Array_Type (Ty)
       and then Contains_Allocated_Parts (Component_Type (Ty));
   --  Access to the reclamation tree of Name at Index

   function New_Move_Tree_Array_Update
     (Name  : W_Prog_Id;
      Index : W_Expr_Array;
      Value : W_Prog_Id;
      Ty    : Entity_Id) return W_Prog_Id
   with
     Pre =>
       Is_Array_Type (Ty)
       and then Contains_Allocated_Parts (Component_Type (Ty));
   --  Update to the reclamation tree of Name at Index with Value

   function New_Move_Tree_Element_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Index     : W_Expr_Array;
      Ty        : Entity_Id) return W_Pred_Id;
   --  Return a predicate stating that move trees at Index in Left_Arr and
   --  Right_Arr are equal.

   function New_Validity_Tree_Array_Access
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id
   with Pre => Is_Array_Type (Ty);
   --  Access to the validity tree of Name at Index

   function New_Validity_Tree_Array_Update
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Value  : W_Expr_Id;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id
   with Pre => Is_Array_Type (Ty);
   --  Update to the validity tree of Name at Index with Value

   function New_Validity_Tree_Slide
     (Tree   : W_Expr_Id;
      Expr   : W_Expr_Id;
      To     : W_Type_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;
   --  Slide the validity tree Tree from the bounds of Expr to the bounds of
   --  To for all its constrained indexes.

   procedure Add_Map_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Arg_Ind : in out Positive);
   --  Add an argument just for the "map" of the array. For constrained arrays,
   --  it is an identity; for unconstrained arrays, it corresponds to the
   --  selection of the corresponding components.

   function Build_Length_Expr
     (Domain      : EW_Domain;
      First, Last : W_Expr_Id;
      Typ         : W_Type_Id := EW_Int_Type) return W_Expr_Id;
   --  Given the terms for first and last, build the expression
   --    if first <= last then last - first + 1 else 0
   --  Beware that the computation may wrap around on bitvectors
   --  @param Domain domain of the transformation
   --  @param First why expression for the first index of the array
   --  @param Last why expression for the last index of the array
   --  @param Typ expected type of the computation
   --  @return if first <= last then last - first + 1 else 0

   function Build_Length_Expr
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id
   with Pre => Is_Constrained (Ty);

   function Build_Length_Expr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id;
   --  Given a type and an array expression, build the length expression for
   --  this array.

   procedure Add_Array_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Arg_Ind : in out Positive);
   --  This procedure is suitable to add the arguments (array, first, last) to
   --  an argument list, and the bounds of other dimensions if the array is not
   --  of dimension 1. The array Args is supposed to be large enough to hold
   --  all these extra arguments starting from the initial value of Arg_Ind.
   --  The final value of Arg_Ind corresponds to the array index that follows
   --  the last argument filled in by this procedure.

   function Get_Array_Attr
     (Expr : W_Term_Id;
      Attr : Attribute_Id;
      Dim  : Positive;
      Typ  : W_Type_Id := EW_Int_Type) return W_Term_Id
   with
     Pre =>
       Attr in Attribute_First | Attribute_Last | Attribute_Length
       and then (Typ = EW_Int_Type or else Why_Type_Is_BitVector (Typ));
   --  Get the expression for the attribute (first/last/length) of the array.
   --  For constrained arrays, this refers to the introduced constant,
   --  for unconstrained arrays this is translated to a field access.
   --  @param Expr the Why3 expression for the array object
   --  @param Attr the querried array attribute
   --  @param Dim dimension of the attribute
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array attribute into Why3

   function Get_Array_Attr
     (Domain : EW_Terms;
      Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Params : Transformation_Params := Body_Params;
      Typ    : W_Type_Id := EW_Int_Type) return W_Term_Id
   with
     Pre =>
       Attr in Attribute_First | Attribute_Last | Attribute_Length
       and then (Typ = EW_Int_Type or else Why_Type_Is_BitVector (Typ));
   --  Same as Get_Array_Attr, can be used when the type is already known.
   --  On unconstrained array types, return bounds used to constrain the index.
   --  @param Domain the term domain to use for bounds
   --  @param Ty the entity for the Ada array type
   --  @param Attr the querried array type attribute
   --  @param Dim dimension of the attribute
   --  @param Params transformation parameters
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array type attribute into Why3

   function Get_Array_Attr
     (Item        : Item_Type;
      Attr        : Attribute_Id;
      Dim         : Positive;
      Ref_Allowed : Boolean;
      Typ         : W_Type_Id := EW_Int_Type) return W_Term_Id;
   --  Get the expression for the attribute (first/last/length) of an array
   --  item.
   --  @param Item the item for the array object
   --  @param Attr the querried array attribute
   --  @param Dim dimension of the attribute
   --  @param Ref_Allowed True if references are allowed in the context.
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array attribute into Why3

   function New_Concat_Call
     (Domain             : EW_Domain;
      Args               : W_Expr_Array;
      Typ                : W_Type_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean) return W_Expr_Id;
   --  Return a call to the concat function in Why array theory

   function New_Const_Call
     (Domain : EW_Domain;
      Elt    : W_Expr_Id;
      Bounds : W_Expr_Array;
      Typ    : W_Type_Id) return W_Expr_Id;
   --  Return a call to the const function in Why array theory

   function New_Logic_Eq_Call
     (Left, Right : W_Term_Id; Domain : EW_Domain) return W_Expr_Id;
   --  Return a call to the logic_eq predicate

   function New_Singleton_Call
     (Domain : EW_Domain; Elt : W_Expr_Id; Pos : W_Expr_Id; Typ : W_Type_Id)
      return W_Expr_Id;
   --  Return a call to the singleton function in Why array theory

   function New_Slice_Call
     (Domain : EW_Domain;
      Arr    : W_Expr_Id;
      Typ    : W_Type_Id;
      Low    : W_Expr_Id;
      High   : W_Expr_Id) return W_Expr_Id;
   --  Return a call to the slice function in Why array theory

   function New_Slice_Call
     (Domain : EW_Domain; Arr : W_Expr_Id; Typ : W_Type_Id) return W_Expr_Id;
   --  Return a call to the slice function in Why array theory

   function New_Well_Formed_Pred (Arr : W_Term_Id) return W_Pred_Id;
   --  Return a call to the well_formed predicate

   function Get_Array_Theory_Name
     (E : Entity_Id; Relaxed_Init : Boolean := False) return Symbol
   with Pre => Is_Type (E) and then Has_Array_Type (E);
   --  @param E the entity of an array type
   --  @param Relaxed_Init True for array modules for wrapper for relaxed
   --         initialization.
   --  @return A name of the form
   --          "Array_(_(Int|BV8|BV16|BV32|BV64|BV128))*__t(__init_wrapper)?"
   --          of the theory associated to the array type E.
   --          The name is the key to this theory in M_Array(_1) hash maps.

   procedure Create_Rep_Array_Theory_If_Needed (E : Entity_Id);
   --  Check if the Array theory of the representation type of E has already
   --  been created. If not create it.
   --  @param E the entity of type array

   procedure Create_Array_Conversion_Theory_If_Needed
     (From : Entity_Id; To : Entity_Id; Relaxed_Init : Boolean := False);
   --  Check if the conversion theory for converting from From to To has
   --  already been created. If not create it.
   --  @param From the entity of source type of the conversion
   --  @param To the entity of target type of the conversion.
   --  @param Relaxed_Init True to convert partially initialized expressions.
   --  ??? Relaxed_Init is always False, is it expected?

   procedure Create_Move_Tree_Theory_For_Array (Th : Theory_UC; E : Entity_Id)
   with Pre => Has_Array_Type (E) and then Contains_Allocated_Parts (E);
   --  Create a module declaring a type for the reclamation trees for objects
   --  of type E.

   procedure Create_Validity_Tree_Theory_For_Array
     (Th : Theory_UC; E : Entity_Id);
   --  Create a module declaring a type for the validity trees for objects
   --  of type E.

   function Get_Array_Theory
     (E : Entity_Id; Relaxed_Init : Boolean := False) return M_Array_Type;
   --  Return the m_array_type containing the theory of the type of E
   --  @param E the entity of type array
   --  @param Relaxed_Init get the theory for wrappers for initialization

   function Get_Array_Theory_1
     (E : Entity_Id; Relaxed_Init : Boolean := False) return M_Array_1_Type;
   --  Return the m_array_1_type containing the theory of the type of E
   --  @param E the entity of type array
   --  @param Relaxed_Init get the theory for wrappers for initialization

   function Get_Array_Theory_1_Comp (E : Entity_Id) return M_Array_1_Comp_Type;
   --  Return the m_array_1_comp_type containing the theory of the type of E
   --  @param E the entity of type array

   function Get_Array_Theory_1_Bool_Op
     (E : Entity_Id) return M_Array_1_Bool_Op_Type;
   --  Return the m_array_1_bool_op_type containing the theory of the type of E
   --  @param E the entity of type array

   function Get_Array_Conversion_Name
     (From, To : Entity_Id; Relaxed_Init : Boolean := False)
      return W_Identifier_Id;
   --  Return the name of the conversion from type From to type To.
   --  @param From the entity of source type of the conversion
   --  @param To the entity of target type of the conversion.
   --  @param Relaxed_Init True to convert partially initialized expressions.
   --  ??? Relaxed_Init is always False, is it expected?

   function Get_Array_Of_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
   with Pre => Has_Init_Wrapper (E);
   --  @param E array type entity
   --  @return the name of the conversion from the wrapper type for E.

   function Get_Array_To_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
   with Pre => Has_Init_Wrapper (E);
   --  @param E array type entity
   --  @return the name of the conversion to the wrapper type for E.

   generic
      with
        function Build_Predicate_For_Comp
          (C_Expr : W_Term_Id; C_Ty : Entity_Id; Idx : W_Expr_Array)
           return W_Pred_Id;
   function Build_Predicate_For_Array
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id;
   --  Construct a predicate:
   --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
   --    ...
   --    Build_Predicate_For_Comp (get <Expr> i1 .. in, [i1 .. in])

   generic
      with
        function Build_Predicate_For_Comp
          (C_Expr1, C_Expr2 : W_Term_Id; C_Ty : Entity_Id; Idx : W_Expr_Array)
           return W_Pred_Id;
   function Build_Binary_Predicate_For_Array
     (Expr1, Expr2 : W_Term_Id; Ty : Entity_Id) return W_Pred_Id;
   --  Construct a predicate:
   --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
   --    ...
   --    Build_Predicate_For_Comp
   --       (get <Expr1> i1 .. in, get <Expr2> i1 .. in, [i1 .. in])

   function Array_Type_Is_Clone (E : Entity_Id) return Boolean;
   --  Return True if we do not produce a new type declaration for E but rather
   --  clone an existing one. Unconstrained array types and constrained type
   --  with dynamic bounds are clones of their base type.
   --  This is used so that we can know if we need to create new references

   function Array_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id
   with Pre => Array_Type_Is_Clone (E);
   --  Return the existing type declaration that has been cloned for E

end Why.Gen.Arrays;
