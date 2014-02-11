------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Snames;              use Snames;
with Types;               use Types;
with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Gen.Expr;        use Why.Gen.Expr;

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
   --  See the file _gnatprove_standard.mlw, the theories Array_N for N =
   --  1,2,3,4 to see this Why model.
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
   --  "Accessing the bounds".
   --
   --  Conversions
   --  -----------
   --
   --  A conversion from an unconstrained object to a constrained one
   --  corresponds to a simple selection of the "elts" field, because the
   --  bounds for the constrained object are provided as constants. Sliding
   --  will take place, and possibly a check inserted.
   --
   --  A conversion between constrained objects is a no-op except for sliding
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
   --  alse [Get_Array_Attr]. Add_Attr_Arg will work with constrained and
   --  unconstrained arrays.

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive);
   --  This variant of Add_Attr_Arg will only work for constrained types

   procedure Declare_Ada_Array
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id);
   --  Introduce all the necessary declarations for an Ada array declaration
   --  Und_Ent is the entity which contains the relevant type information (the
   --  underlying type)

   function New_Array_Access
     (Ada_Node  : Node_Id;
      Ar        : W_Expr_Id;
      Index     : W_Expr_Array;
      Domain    : EW_Domain) return W_Expr_Id;
   --  Generate an expr that corresponds to an array access.

   function Array_Convert_To_Base
     (Domain    : EW_Domain;
      Ar        : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Base_Type (Get_Type (Ar)) = EW_Abstract;
   --  "Ar" must be a Why expression of unconstrained array type. Convert it to
   --  the "split" view of UC arrays

   function Array_Convert_From_Base
     (Domain    : EW_Domain;
      Ar        : W_Expr_Id) return W_Expr_Id
   with Pre => Get_Base_Type (Get_Type (Ar)) = EW_Split;
   --  "Ar" must be a Why expression of unconstrained array type, in split
   --  form. Convert it to the regular unconstrained form.

   function Array_Convert_From_Base
     (Domain    : EW_Domain;
      Target    : Entity_Id;
      Ar        : W_Expr_Id;
      First     : W_Expr_Id;
      Last      : W_Expr_Id) return W_Expr_Id;
   --  This variant can be used when we need to build an unconstrained array,
   --  but "Ar" is not in split form. We need to provide the target type and
   --  first/last expressions explicitly.

   function New_Array_Update
      (Ada_Node  : Node_Id;
       Ar        : W_Expr_Id;
       Index     : W_Expr_Array;
       Value     : W_Expr_Id;
       Domain    : EW_Domain) return W_Expr_Id;

   function New_Element_Equality
     (Ada_Node   : Node_Id := Empty;
      Left_Arr   : W_Expr_Id;
      Right_Arr  : W_Expr_Id;
      Index      : W_Expr_Array) return W_Pred_Id;
   --  Return a predicate of the form:
   --
   --    <left_arr>[<index>] = <right_arr>[<index>]

   procedure Add_Map_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Arg_Ind : in out Positive);
   --  Add an argument just for the "map" of the array. For constrained arrays,
   --  this is the identity, for unconstrained arrays, this corresponds to the
   --  selection of the corresponding field.

   function Build_Length_Expr
     (Domain : EW_Domain;
      First, Last : W_Expr_Id) return W_Expr_Id;
   --  Given the terms for first and last, build the expression
   --    if first <= last then last - first + 1 else 0

   function Build_Length_Expr
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Dim    : Positive) return W_Expr_Id;

   function Build_Length_Expr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Dim    : Positive) return W_Expr_Id;
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
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Attr   : Attribute_Id;
      Dim    : Positive) return W_Expr_Id
     with Pre =>
       Attr in Attribute_First | Attribute_Last | Attribute_Length;
   --  Get the expression for the attribute (first/last) of the array.
   --  For constrained arrays, this refers to the introduced constant,
   --  for unconstrained arrays this is translated to a field access.

   function Get_Array_Attr
     (Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive) return W_Expr_Id;
   --  Same as Get_Array_Attr, can be used when the type is already known

   function New_Concat_Call
     (Domain : EW_Domain;
      Args   : W_Expr_Array;
      Typ    : W_Type_Id) return W_Expr_Id;
   --  return a call to the concat function in Why array theory

   function New_Singleton_Call
     (Domain : EW_Domain;
      Elt    : W_Expr_Id;
      Pos    : W_Expr_Id) return W_Expr_Id;
   --  return a call to the singleton function in Why array theory

end Why.Gen.Arrays;
