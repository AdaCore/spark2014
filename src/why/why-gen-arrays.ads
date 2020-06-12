------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;

package Why.Gen.Arrays is
   --  This package encapsulates the encoding of Ada arrays into Why.
   --
   --  --------------------
   --  Modeling Array types
   --  --------------------
   --
   --  The operations on array *content* (access, update, sliding)
   --  are modeled in Why by a simple "map" type that maps indices (a simple
   --  "int" in the one-dimensional case) to objects of the component type.
   --  There are only three functions on this type:
   --    - "get" to access the map at a certain index
   --    - "set" to update the map at a certain index
   --    - "slide" to shift the objects of the map
   --
   --  There is also a predicate to express boolean equality.
   --
   --  See the file _gnatprove_standard.mlw, the theories Array__N for N =
   --  1,2,3,... to see this Why model.
   --
   --  The Why model of constrained array types consists of this map type,
   --  along with two constants "first" and "last" that model the bounds of
   --  this type. See ada__model.mlw, the theories Constr_Array_N for this
   --  encoding.
   --
   --  The Why model of unconstrained array types consists of a record with
   --  two components: the map, and a special "index" object that encodes the
   --  bounds and their properties. See ada__model.mlw, the theories
   --  Unconstr_Array_N for this encoding.
   --
   --  -------------------------
   --  Modeling Array operations
   --  -------------------------

   --  Indexing and Assignment
   --  -----------------------
   --
   --  Indexing and Assignment are directly expressed using the "get" and
   --  "set" operations on the map type. No shifting of the index takes place,
   --  "A (I)" in Ada directly becomes "get <array object> i" in Why. For
   --  constrained arrays, nothing else is there to do.
   --
   --  For unconstrained arrays the array object must be converted to the map
   --  type (by selecting the component) prior to indexing. For assignment,
   --  the Why record update syntax is used:
   --
   --    { x with elts = update x.elts i v }
   --
   --  Slicing
   --  -------
   --
   --  Slicing is in fact an operation on the array bounds, and not the
   --  content. For constrained arrays, there is nothing to do (the frontend
   --  generates the appropriate subtypes already) except for runtime checks.
   --  For unconstrained arrays, the content is selected.
   --
   --  Sliding
   --  -------
   --
   --  Sliding happens when converting to a constrained array type. We use the
   --  "slide" function for that.
   --
   --  Accessing bounds of the type or the object
   --  ------------------------------------------
   --
   --  For constrained types, the type declaration comes with the appropriate
   --  constants, and T'First for a constrained array type T, and X'First for
   --  a constrained array object X is simply translated to this constant.
   --
   --  For unconstrained array objects, the bounds are stored in the object
   --  and retrieved with the appropriate selection.
   --
   --  Equality
   --  --------
   --
   --  Equality on arrays is simply translated by a call to the generic
   --  "bool_eq" function, which requires explicit passing of the bounds. See
   --  "Accessing bounds".
   --
   --  Conversions
   --  -----------
   --
   --  A conversion from an unconstrained object to a constrained one
   --  corresponds to a simple selection of the "elts" field, because the
   --  bounds for the constrained object are provided as constants. Sliding
   --  will take place, and possibly a check inserted.
   --
   --  A conversion between constrained objects is a no-op except for sliding,
   --  if necessary.
   --
   --  A conversion from constrained objects to an unconstrained type requires
   --  building an unconstrained object, by providing the "elts" field (= the
   --  constrained object) and the bounds (the constants of the type).
   --
   --  A conversion between unconstrained objects is similar, but the bounds
   --  are retrieved from the object instead of the type.

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
   with Pre => Is_Constrained (Ty);
   --  This variant of Add_Attr_Arg will only work for constrained types

   procedure Declare_Ada_Array
     (File : W_Section_Id;
      E    : Entity_Id);
   --  Introduce all the necessary declarations for an Ada array declaration;
   --  E is the entity which contains the relevant type information (the
   --  underlying type).

   procedure Declare_Init_Wrapper_For_Array
     (File : W_Section_Id;
      E    : Entity_Id) with
     Pre => Has_Array_Type (E) and then Might_Contain_Relaxed_Init (E);
   --  Introduce necessary declarations for the wrapper type for E

   procedure Declare_Additional_Symbols_For_String (Section : W_Section_Id);
   --  Declare to_string and of_string functions used for 'Image and 'Value
   --  attributes.

   function New_Array_Access
     (Ada_Node : Node_Id;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Domain   : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to an array access

   function Array_Convert_To_Base
     (Domain : EW_Domain;
      Ar     : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Type_Kind (Get_Type (Ar)) = EW_Abstract;
   --  "Ar" must be a Why expression of unconstrained array type. Convert it to
   --  the "split" view of UC arrays

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ar     : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Type_Kind (Get_Type (Ar)) = EW_Split;
   --  "Ar" must be a Why expression of unconstrained array type, in split
   --  form. Convert it to the regular unconstrained form.

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Target : Entity_Id;
      Ar     : W_Expr_Id;
      First  : W_Expr_Id;
      Last   : W_Expr_Id) return W_Expr_Id;
   --  This variant can be used when we need to build an unconstrained array,
   --  but "Ar" is not in split form. We need to provide the target type and
   --  first/last expressions explicitly.

   function Array_Convert_From_Base
     (Domain   : EW_Domain;
      Old_Ar   : W_Expr_Id;
      New_Base : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Type_Kind (Get_Type (New_Base)) = EW_Split;
   --  "New_Base" must be a Why expression of unconstrained array type, in
   --  split form. Convert it to the regular unconstrained form, using Old_Ar's
   --  bounds.

   function New_Array_Range_Expr
     (Index_Expr : W_Expr_Id;
      Array_Expr : W_Expr_Id;
      Domain     : EW_Domain;
      Dim        : Positive)
      return W_Expr_Id;
   --  Construct an expression stating that an index is in an array's bound.
   --  @param Index_Expr expression for the considered index
   --  @param Array_Expr expression for the array
   --  @param Domain expected domain of the range expression
   --  @param Dim considered index in the array
   --  @param an expression
   --  <array_expr>.first<dim> <= <index_expr> <= <array_expr>.last<dim>

   function New_Array_Update
      (Ada_Node  : Node_Id;
       Ar        : W_Expr_Id;
       Index     : W_Expr_Array;
       Value     : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;
   --  ???

   function New_Bounds_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Dim       : Positive) return W_Pred_Id;
   --  @param Left_Arr array expression whose bounds should be compared
   --  @param Right_Arr
   --  @param Dim number of dimensions in the arrays
   --  @return a predicate of the form:
   --
   --    <left_arr>.first1 = <right_arr>.first1 /\
   --    <left_arr>.last1 = <right_arr>.last1 /\ ...

   function New_Bounds_Equality
     (Left_Arr : W_Expr_Id;
      Right_Ty : Entity_Id;
      Domain   : EW_Domain := EW_Pred;
      Params   : Transformation_Params := Body_Params) return W_Expr_Id
   with Pre => Is_Constrained (Right_Ty);
   --  same as above but takes the bounds of a type for Right

   function New_Bounds_Equality
     (Left_Arr     : W_Expr_Id;
      Right_Bounds : W_Expr_Array;
      Dim          : Positive;
      Domain       : EW_Domain := EW_Pred) return W_Expr_Id
   with Pre => Right_Bounds'Length = Dim * 2;
   --  same as above but with the bounds stored in an array

   function New_Length_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Dim       : Positive) return W_Pred_Id;
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
     (Left_Arr : W_Expr_Id;
      Right    : Entity_Id;
      Dim      : Positive) return W_Pred_Id
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
      Typ         : W_Type_Id := EW_Int_Type)
      return W_Expr_Id;
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

   function Get_Entity_Of_Variable (E : W_Expr_Id) return Entity_Id
     with Pre => Get_Type_Kind (Get_Type (E)) in EW_Split;
   --  Return the Ada entity associated to an array expression in split form.
   --  There is always one or we cannot reach to the object's bounds.
   --  @param E Why expression for which we want an ada entity.
   --  @result Ada entity associated to E that can be used to find its bounds.

   function Get_Array_Attr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id
     with Pre =>
       Attr in Attribute_First | Attribute_Last | Attribute_Length
       and then (Typ = EW_Int_Type or else Why_Type_Is_BitVector (Typ));
   --  Get the expression for the attribute (first/last/length) of the array.
   --  For constrained arrays, this refers to the introduced constant,
   --  for unconstrained arrays this is translated to a field access.
   --  @param Domain the domain of the returned expression
   --  @param Expr the Why3 expression for the array object
   --  @param Attr the querried array attribute
   --  @param Dim dimension of the attribute
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array attribute into Why3

   function Get_Array_Attr
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Params : Transformation_Params := Body_Params;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id
     with Pre =>
       Attr in Attribute_First | Attribute_Last | Attribute_Length
       and then (Typ = EW_Int_Type or else Why_Type_Is_BitVector (Typ));
   --  Same as Get_Array_Attr, can be used when the type is already known.
   --  On unconstrained array types, return bounds used to constrain the index.
   --  @param Domain The domain of the returned expression.
   --  @param Ty the entity for the Ada array type
   --  @param Attr the querried array type attribute
   --  @param Dim dimension of the attribute
   --  @param Params transformation parameters
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array type attribute into Why3

   function New_Concat_Call
     (Domain             : EW_Domain;
      Args               : W_Expr_Array;
      Typ                : W_Type_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean) return W_Expr_Id;
   --  Return a call to the concat function in Why array theory

   function New_Singleton_Call
     (Domain : EW_Domain;
      Elt    : W_Expr_Id;
      Pos    : W_Expr_Id;
      Typ    : W_Type_Id) return W_Expr_Id;
   --  Return a call to the singleton function in Why array theory

   function Get_Array_Theory_Name
     (E            : Entity_Id;
      Init_Wrapper : Boolean := False) return Symbol
   with Pre => Is_Type (E) and then Has_Array_Type (E);
   --  @param E the entity of an array type
   --  @param Init_Wrapper True for array modules for wrapper for relaxed
   --         initialization.
   --  @return A name of the form
   --          "Array_(_(Int|BV8|BV16|BV32|BV64))*__t(__init_wrapper)?"
   --          of the theory associated to the array type E.
   --          The name is the key to this theory in M_Array(_1) hash maps.

   procedure Create_Rep_Array_Theory_If_Needed
     (File          : W_Section_Id;
      E             : Entity_Id;
      Register_Only : Boolean := False);
   --  Check if the Array theory of the representation type of E has already
   --  been created. If not create it.
   --  @param File the current why file
   --  @param E the entity of type array
   --  @param Register_Only if Register_Only is true, the declaration is not
   --         emited.

   procedure Create_Array_Conversion_Theory_If_Needed
     (Current_File : W_Section_Id;
      From         : Entity_Id;
      To           : Entity_Id;
      Init_Wrapper : Boolean := False);
   --  Check if the conversion theory for converting from From to To has
   --  already been created. If not create it.
   --  @param File the current file section. Conversion theories are always
   --     created in WF_Pure, but it may be necessary to save the currently
   --     opened theory if Current_File = WF_Pure.
   --  @param From the entity of source type of the conversion
   --  @param To the entity of target type of the conversion.
   --  @param Init_Wrapper True to convert partially initialized expressions.

   function Get_Array_Theory
     (E            : Entity_Id;
      Init_Wrapper : Boolean := False) return M_Array_Type;
   --  Return the m_array_type containing the theory of the type of E
   --  @param E the entity of type array
   --  @param Init_Wrapper get the theory for wrappers for initialization

   function Get_Array_Theory_1
     (E            : Entity_Id;
      Init_Wrapper : Boolean := False) return M_Array_1_Type;
   --  Return the m_array_1_type containing the theory of the type of E
   --  @param E the entity of type array
   --  @param Init_Wrapper get the theory for wrappers for initialization

   function Get_Array_Theory_1_Comp (E : Entity_Id) return M_Array_1_Comp_Type;
   --  Return the m_array_1_comp_type containing the theory of the type of E
   --  @param E the entity of type array

   function Get_Array_Theory_1_Bool_Op
     (E : Entity_Id) return M_Array_1_Bool_Op_Type;
   --  Return the m_array_1_bool_op_type containing the theory of the type of E
   --  @param E the entity of type array

   function Get_Array_Conversion_Name
     (From, To     : Entity_Id;
      Init_Wrapper : Boolean := False) return W_Identifier_Id;
   --  Return the name of the conversion from type From to type To.
   --  @param From the entity of source type of the conversion
   --  @param To the entity of target type of the conversion.
   --  @param Init_Wrapper True to convert partially initialized expressions.

   function Get_Array_Of_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
     with Pre => Might_Contain_Relaxed_Init (E);
   --  @param E array type entity
   --  @return the name of the conversion from the wrapper type for E.

   function Get_Array_To_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
     with Pre => Might_Contain_Relaxed_Init (E);
   --  @param E array type entity
   --  @return the name of the conversion to the wrapper type for E.

   generic
      with function Build_Predicate_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id) return W_Pred_Id;
   function Build_Predicate_For_Array
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id;
   --  Construct a predicate:
   --  forall i1 .. in : int. in_range i1 /\ .. /\ in_range in ->
   --    Build_Predicate_For_Comp (get <Expr> i1 .. in)

   function Array_Type_Is_Clone (E : Entity_Id) return Boolean;
   --  Return True if we do not produce a new type declaration for E but rather
   --  clone an existing one. Unconstrained array types and constrained type
   --  with dynamic bounds are clones of their base type.
   --  This is used so that we can know if we need to create new references

   function Array_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id with
     Pre => Array_Type_Is_Clone (E);
   --  Return the existing type declaration that has been cloned for E

end Why.Gen.Arrays;
