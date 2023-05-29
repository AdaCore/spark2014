------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Checked_Types;          use Checked_Types;
with Common_Containers;      use Common_Containers;
with GNATCOLL.Symbols;       use GNATCOLL.Symbols;
with Snames;                 use Snames;
with SPARK_Util;             use SPARK_Util;
with Types;                  use Types;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Ids;                use Why.Ids;
with Why.Inter;              use Why.Inter;
with Why.Sinfo;              use Why.Sinfo;
with Why.Types;              use Why.Types;

package Why.Gen.Names is
   --  This package provides ways to manipulate subprogram names and
   --  to create identifiers from their string representation

   procedure Initialize;
   --  Initialize the state of this package; should be called before using the
   --  NID function.

   procedure Free;
   --  Release memory used to store names

   function NID (Name : String) return Symbol;
   --  Return Symbol for Name

   function Conversion_Name
      (From : W_Type_Id;
       To   : W_Type_Id) return W_Identifier_Id
     with Pre =>
       (if Get_Type_Kind (From) = EW_Builtin
          and then Get_Type_Kind (To) in EW_Abstract | EW_Split
        then Base_Why_Type (To) = From
        elsif Get_Type_Kind (To) = EW_Builtin
          and then Get_Type_Kind (From) in EW_Abstract | EW_Split
        then Base_Why_Type (From) = To);
   --  Return the name of the conversion function between the two types

   function Range_Pred_Name
     (Ty : Entity_Id) return W_Identifier_Id;
   --  Return the name of the "in_range" predicate for the type

   function Dynamic_Prop_Name
     (Ty : Entity_Id) return W_Identifier_Id;
   --  Return the name of the "dynamic_property" predicate for the type

   function Range_Check_Name
     (Ty : Entity_Id; R : Scalar_Check_Kind) return W_Identifier_Id;
   --  Return the name of the "range_check_" program function for the type

   function New_Division (Kind : W_Type_Id) return W_Identifier_Id;
   --  Return the name of the division for the given kind

   function New_Exp (Kind : W_Type_Id) return W_Identifier_Id;
   --  Return the name of the exponential for the given kind

   function New_Abs (Kind : W_Type_Id) return W_Identifier_Id;
   --  Return the name of the absolute value operator for the given kind

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Name     : String;
      Typ      : W_Type_Id := Why.Types.Why_Empty;
      Attrs    : String_Sets.Set := String_Sets.Empty_Set)
      return W_Identifier_Id;
   --  Create a new term identifier for Name and return the result

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Name      : String;
      Namespace : Symbol := No_Symbol;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Attrs     : String_Sets.Set := String_Sets.Empty_Set)
      return W_Identifier_Id;

   function New_Identifier
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : String;
      Typ      : W_Type_Id := Why.Types.Why_Empty;
      Attrs    : String_Sets.Set := String_Sets.Empty_Set)
      return W_Identifier_Id;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : String;
      Namespace : Symbol := No_Symbol;
      Module    : W_Module_Id;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Attrs     : String_Sets.Set := String_Sets.Empty_Set)
      return W_Identifier_Id;

   function New_Identifier (Name : W_Name_Id) return W_Identifier_Id;

   function New_Identifier
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Symb      : Symbol;
      Namespace : Symbol := No_Symbol;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Module    : W_Module_Id := Why.Types.Why_Empty;
      Infix     : Boolean := False;
      Attrs     : String_Sets.Set := String_Sets.Empty_Set)
      return W_Identifier_Id;

   function New_Temp_Identifier (Base_Name : String := "") return String;
   --  @param Base_Name optional basis for the name of the temporary
   --  @return a new unique identifier, either based on Base_Name when provided
   --     or otherwise dependent on the current compilation unit

   function New_Temp_Identifier
     (Ada_Node  : Node_Id   := Empty;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Base_Name : String    := "") return W_Identifier_Id;
   --  @param Base_Name optional basis for the name of the temporary
   --  @return a new unique identifier

   function New_Generated_Identifier
     (Ada_Node  : Node_Id   := Empty;
      Typ       : W_Type_Id := Why.Types.Why_Empty;
      Base_Name : String    := "";
      Attrs     : String_Sets.Set) return W_Identifier_Id;

   function New_Temp_Identifiers
     (Num : Positive;
      Typ : W_Type_Id) return W_Identifier_Array;
   --  Return an array of new unique identifiers with Num elements

   function New_Module
     (Ada_Node : Node_Id := Empty;
      File     : Symbol;
      Name     : String)
      return W_Module_Id;
   --  Build a new module id with the given File and Name elements. The Name
   --  will be capitalized because that's required by Why3 syntax.

   function New_Result_Ident (Typ : W_Type_Id) return W_Identifier_Id;

   function To_Exprs (Ids : W_Identifier_Array) return W_Expr_Array;
   --  Conversion each element of Ids to exprs and return the result

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id;
   --  Create a new identifier for an entity in program space, given
   --  the name of the corresponding entity in logic space.

   function Logic_Function_Name
     (E                      : Function_Kind_Id;
      Selector_Name          : Selection_Kind := Why.Inter.Standard;
      Specialization_Module  : Symbol := No_Symbol)
      return W_Identifier_Id;
   --  Compute the name to be used to call a function or a function profile in
   --  the logic domain. If Specialization_Module is supplied, then the name is
   --  taken from the M_HO_Specializations map.

   function Guard_Predicate_Name
     (E                      : Function_Kind_Id;
      Selector_Name          : Selection_Kind := Why.Inter.Standard;
      Specialization_Module  : Symbol := No_Symbol)
      return W_Identifier_Id;
   --  Compute the name to be used for the guard of a function or a function
   --  profile. If Specialization_Module is supplied, then the name is taken
   --  from the M_HO_Specializations map.

   Def_Axiom : constant String := "def_axiom";
   --  suffix for a definition axiom

   Post_Axiom          : constant String := "post_axiom";
   Post_Dispatch_Axiom : constant String := "post__dispatch_axiom";
   Post_Refine_Axiom   : constant String := "post_refine_axiom";
   --  suffix for a postcondition axiom

   Compat_Axiom        : constant String := "compat_axiom";
   --  suffix for compatibility axiom suffix for dispatching calls

   Function_Guard      : constant String := "function_guard";
   --  suffix for guards of functions defining axioms
   Specific_Post       : constant String := "specific_post";
   --  suffix for specific postcondition of dispatching procedures

   Pledge_Axiom        : constant String := "pledge_axiom";
   --  suffix for defining axiom for pledges of traversal expression functions

   --  Labels for counterexamples:
   Constrained_Label : constant String := "Constrained";
   Discr_Label       : constant String := "Discriminants";
   Field_Label       : constant String := "Fields";
   First_Label       : constant String := "First";
   Last_Label        : constant String := "Last";
   Is_Null_Label     : constant String := "Is_Null";
   All_Label         : constant String := "All";
   Init_Val_Label    : constant String := "Init_Val";
   Initialized_Label : constant String := "Initialized";
   Index_Label       : constant String := "Index";
   Loop_Entry_Label  : constant String := "Loop_Entry";
   Old_Label         : constant String := "Old";

   --  The following enumeration is used for two things:
   --    * a simple enumeration of strings, accessed using the "To_String"
   --      function below. In practice, many of these strings are used to build
   --      Why identifiers. To_String is also used in various *Append
   --      functions.
   --    * as a way to identify Why3 identifiers that belong to specific Ada
   --      entities, accessed using the E_Symb function in Why.Atree.Modules.
   --  Note that the first way of these is considered deprecated, instead use
   --  the E_Symb function if possible (and register the required symbols using
   --  Insert_Symbols in Why.Atree.Modules)

   type Why_Name_Enum is
     (
      --  Suffix appended to the name of an object to build the name of
      --  the aggregate function used as initialization expression in the
      --  declaration of the object.
      WNE_Aggregate_Def_Suffix,

      WNE_Array_Base_Range_Pred,
      WNE_Array_Base_Range_Pred_2,
      WNE_Array_Base_Range_Pred_3,
      WNE_Array_Base_Range_Pred_4,
      WNE_Array_Component_Type,
      WNE_Array_Elts,
      WNE_Array_Type,

      --  Prefixes and Suffixes used to compose representative array theory
      --  names.
      WNE_Array_BV_Suffix, --  Suffix for arrays ranging over modulars
      WNE_Array_Comparison_Suffix, --  Suffix for comparison operators module
      WNE_Array_Concatenation_Suffix, --  Suffix for concatenation module
      WNE_Array_Int_Suffix, --  Suffix for arrays ranging over signed integers
      WNE_Array_Logical_Op_Suffix, --  Suffix for logical operators module
      WNE_Array_Prefix, --  Prefix of array modules

      WNE_Attr_Access,
      WNE_Attr_Alignment,
      WNE_Attr_Component_Size,
      WNE_Attr_Constrained,
      WNE_Attr_First,
      WNE_Attr_First_2,
      WNE_Attr_First_3,
      WNE_Attr_First_4,
      WNE_Attr_First_Bit,
      WNE_Attr_Image,
      WNE_Attr_Last,
      WNE_Attr_Last_2,
      WNE_Attr_Last_3,
      WNE_Attr_Last_4,
      WNE_Attr_Last_Bit,
      WNE_Attr_Length,
      WNE_Attr_Length_2,
      WNE_Attr_Length_3,
      WNE_Attr_Length_4,
      WNE_Attr_Modulus,
      WNE_Attr_Object_Size,
      WNE_Attr_Position,
      WNE_Attr_Value_Size,
      WNE_Attr_Tag,

      --  Numerator and denominator for the "small" of a fixed-point type
      WNE_Small_Num,
      WNE_Small_Den,

      WNE_Attr_Value,

      --  Used to translate the Enum_Rep and Enum_Val attributes
      WNE_Pos_To_Rep,
      WNE_Rep_To_Pos,

      --  Suffix of the module giving the axiom defining a logic function
      WNE_Axiom_Suffix,  --  ___axiom

      WNE_Bool_Eq,
      WNE_User_Eq,
      WNE_Check_Not_First,
      WNE_Check_Not_Last,
      WNE_Default_Init,            --  assumption for default initialization
      WNE_Dispatch_Eq,
      WNE_Dummy,
      WNE_Dynamic_Property,
      WNE_Dynamic_Property_BV_Int, --  for bitvector when index of an array

      WNE_Dynamic_Invariant,       --  dynamic invariant of a type

      WNE_Type_Invariant,          --  toplevel invariant checking function

      --  Name of the program function for type invariant checks on subprogram
      --  calls.
      WNE_Check_Invariants_On_Call,

      --  Name of the program function for variant checks on subprogram calls
      WNE_Check_Subprogram_Variants,

      --  Symbols to introduce a bijection between an abstract type and its
      --  completion.
      WNE_Open,
      WNE_Close,

      --  Prefix for Why3 field names corresponding to record components
      WNE_Rec_Comp_Prefix,

      --  Prefix for Why3 parameters corresponding to subprogram parameters
      WNE_Param_Prefix,

      --  Symbols for extensions of tagged types

      --  Name of the Why3 field representing potential unknown extension
      --  components in a tagged derivation.
      WNE_Hidden_Extension,  --  rec__hidden_ext__

      --  Type for the extension components of a tagged type
      WNE_Extension_Type,    --  __ext_type

      --  Constant standing for the empty extension
      WNE_Null_Extension,    --  __null_ext__

      --  Name of the Why3 field representing extension components in a tagged
      --  type or a class-wide type.
      WNE_Rec_Extension,     --  rec__ext__

      --  Suffix of the above extension field, to be used in related functions
      WNE_Rec_Extension_Suffix,  --  ext__

      --  Name of the record type in a representative record theory
      WNE_Rec_Rep,

      --  Name of constant tag value for a tagged type
      WNE_Tag,  --  __tag

      --  Name of the function aggregating the extension components and the
      --  special extension field rec__ext__ in the derived type, to generate
      --  a value of the special extension field rec__ext__ in the root type.
      WNE_Hide_Extension,  --  hide_ext__

      --  Name of the type of the private parts of a record
      WNE_Private_Type,
      --  Name of equality on this type
      WNE_Private_Eq,
      --  Dummy symbol of this type
      WNE_Private_Dummy,

      --  Division operators for a fixed-point type
      WNE_Fixed_Point_Div,
      WNE_Fixed_Point_Div_Int,
      WNE_Fixed_Point_Prefix,          --  Prefix of fixed point modules
      WNE_Fixed_Point_Mult_Div_Prefix, --  Prefix of mult/div modules

      --  Multiplication operators for a fixed-point type
      WNE_Fixed_Point_Mult,
      WNE_Fixed_Point_Mult_Int,

      WNE_Index_Dynamic_Property,
      WNE_Index_Dynamic_Property_2,
      WNE_Index_Dynamic_Property_3,
      WNE_Index_Dynamic_Property_4,

      --  Predefined projection for why range types
      WNE_Int_Proj,

      --  Prefix for name of functions which extract the value of an extension
      --  component from the extension field of a value of the root type.
      WNE_Extract_Prefix,

      --  Name of module containing the functions which correspond to the
      --  dispatching version of a primitive operation of a tagged type.
      WNE_Dispatch_Module,  --  Dispatch

      --  Name of module containing the functions which correspond to the
      --  no-return version of an error-signaling procedure.
      WNE_No_Return_Module,  --  No_Return

      --  Name of module containing the function which corresponds to the
      --  refined version (refined_post) of a subprogram.
      WNE_Refine_Module,  --  Refine

      --  Names of predicates for functions guards
      WNE_Func_Guard,
      WNE_Refined_Func_Guard,
      WNE_Dispatch_Func_Guard,

      --  Name of predicate for specific post
      WNE_Specific_Post,

      --  Suffixes for handling of references
      WNE_Ref,
      WNE_Content,
      WNE_Havoc,

      WNE_Of_Array,
      WNE_Of_Base,
      WNE_Of_Rep,
      WNE_Of_Int,
      WNE_Of_Fixed,
      WNE_Of_Real,                --  for fixed-point
      WNE_Of_Float32,             --  for fixed-point
      WNE_Of_Float64,             --  for fixed-point
      WNE_Of_BitVector,
      WNE_Range_Check_Fun,
      WNE_Range_Check_Fun_BV_Int, --  for conversion from int to bitvector
      WNE_Rec_Split_Discrs,
      WNE_Rec_Split_Fields,
      WNE_Range_Pred,
      WNE_Range_Pred_BV_Int,      --  range predicate on bv with ints
      WNE_To_Array,
      WNE_To_Base,
      WNE_To_Rep,
      WNE_To_Int,
      WNE_To_Int_2,
      WNE_To_Int_3,
      WNE_To_Int_4,
      WNE_To_Fixed,
      WNE_To_Float32,             --  for fixed-point
      WNE_To_Float64,             --  for fixed-point

      WNE_Empty,                   --  dummy value for Why_Name_Enum

      --  Names related to the pointer type
      WNE_Null_Pointer,           --  "__null_pointer"
      WNE_Is_Null_Pointer,        --  "__is_null_pointer"
      WNE_Is_Moved_Field,         --  "rec__is_moved__"
      WNE_Pointer_Value,          --  "__pointer_value"
      WNE_Assign_Null_Check,      --  "__assign_null_check"
      WNE_Pointer_Value_Abstr,    --  "__pointer_value_abstr"
      WNE_Is_Moved,               --  "__is_moved"
      WNE_Move,                   --  "__move"
      WNE_Moved_Relation,         --  "__moved_relation"
      WNE_Pointer_Call,           --  "__call_"

      --  Names related to initialization checks
      WNE_Init_Value,             --  "rec__value"
      WNE_Init_Wrapper_Suffix,    --  "__init_wrapper"
      WNE_Attr_Init,              --  "attr__init"
      WNE_To_Wrapper,             --  "to_wrapper"
      WNE_Of_Wrapper,             --  "of_wrapper"
      WNE_Private_To_Wrapper,     --  "__main_to_wrapper"
      WNE_Private_Of_Wrapper      --  "__main_of_wrapper"
     );

   function Attr_To_Why_Name (A : Attribute_Id) return Why_Name_Enum;

   function Attr_Append (Base     : String;
                         A        : Attribute_Id;
                         Count    : Positive;
                         Typ      : W_Type_Id;
                         Module   : W_Module_Id := Why.Types.Why_Empty;
                         Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function Attr_Append (Base  : W_Identifier_Id;
                         A     : Attribute_Id;
                         Count : Positive;
                         Typ   : W_Type_Id) return W_Identifier_Id;

   function Discr_Append (Base : W_Identifier_Id;
                          Typ  : W_Type_Id) return W_Identifier_Id;

   function Field_Append (Base : W_Identifier_Id;
                          Typ  : W_Type_Id) return W_Identifier_Id;

   function Ref_Append (Base : W_Name_Id) return W_Name_Id;

   function Content_Append (Base : W_Name_Id;
                            Typ  : W_Type_Id) return W_Identifier_Id;

   function Value_Append (Base : W_Identifier_Id;
                          Typ  : W_Type_Id) return W_Identifier_Id;

   function Is_Null_Append (Base : W_Identifier_Id;
                            Typ  : W_Type_Id) return W_Identifier_Id;

   function Is_Moved_Append (Base : W_Identifier_Id;
                             Typ  : W_Type_Id) return W_Identifier_Id;

   function Init_Append (Base : W_Identifier_Id) return W_Identifier_Id;

   function Havoc_Append (Base : W_Name_Id) return W_Identifier_Id;

   function Variant_Append
     (Base     : String;
      Count    : Positive;
      Typ      : W_Type_Id;
      Module   : W_Module_Id := Why.Types.Why_Empty;
      Ada_Node : Node_Id := Empty) return W_Identifier_Id;

   function To_String (W : Why_Name_Enum) return String;

   function To_Ident (W        : Why_Name_Enum;
                      Ada_Node : Node_Id := Empty)
                      return W_Identifier_Id;

   function To_Name (W : Why_Name_Enum) return W_Name_Id;

   function To_Local (Name : W_Identifier_Id) return W_Identifier_Id;
   function To_Local (Name : W_Identifier_Id) return W_Name_Id;
   function To_Local (Name : W_Name_Id) return W_Name_Id;
   --  @param Name a possibly fully qualified identifier
   --  @return the identifier or name where the module component has been
   --    removed

   function WNE_Array_Base_Range_Pred (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_Array_Base_Range_Pred
   --  @param I an index between 1 and 4 selectind the dimension

   function WNE_Attr_First (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_Attr_First_X
   --  @param I an index between 1 and 4 selecting the dimension

   function WNE_Attr_Last (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_Attr_Last_X
   --  @param I an index between 1 and 4 selectind the dimension

   function WNE_Attr_Length (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_Attr_Last_X
   --  @param I an index between 1 and 4 selectind the dimension

   function WNE_Index_Dynamic_Property (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_Index_Dynamic_Property
   --  @param I an index between 1 and 4 selectind the dimension

   function WNE_To_Int (I : Integer) return Why_Name_Enum;
   --  wrapper function for the enumeration literals WNE_To_Int_X
   --  @param I an index between 1 and 4 selectind the dimension

   function Get_Modular_Converter_Range_Check
     (From, To : W_Type_Id) return W_Identifier_Id;
   --  @param From the BV type to convert from
   --  @param To the BV type to convert to
   --  @return the appropriate range check function

end Why.Gen.Names;
