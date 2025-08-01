------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          S P A R K _ A T R E E                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2025, AdaCore                     --
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

with Atree;
with Einfo.Entities;
with Exp_Util;
with Namet;  use Namet;
with Sem_Aggr;
with Sem_Aux;
with Sem_Eval;
with Sem_Util;
with Sinfo.Nodes;
use all type Sinfo.Nodes.Node_Kind;
with Sinfo.Utils;
with Snames; use Snames;
with SPARK_Util;
with Types;  use Types;
with Uintp;  use Uintp;
with Urealp; use Urealp;

package SPARK_Atree is

   package SN renames Sinfo.Nodes;

   --  Renamings are either
   --  * trivial in the .ads file or
   --  * with Pre/Post contract completed-by-renaming in the .adb file.

   subtype Node_Kind is SN.Node_Kind;

   subtype N_Binary_Op is SN.N_Binary_Op;
   subtype N_Delay_Statement is SN.N_Delay_Statement;
   subtype N_Declaration is SN.N_Declaration;
   subtype N_Entity is SN.N_Entity;
   subtype N_Has_Entity is SN.N_Has_Entity;
   subtype N_Has_Etype is SN.N_Has_Etype;
   subtype N_Membership_Test is SN.N_Membership_Test;
   subtype N_Op is SN.N_Op;
   subtype N_Op_Compare is SN.N_Op_Compare;
   subtype N_Op_Shift is SN.N_Op_Shift;
   subtype N_Raise_xxx_Error is SN.N_Raise_xxx_Error;
   subtype N_Short_Circuit is SN.N_Short_Circuit;
   subtype N_Subexpr is SN.N_Subexpr;
   subtype N_Subprogram_Call is SN.N_Subprogram_Call;
   subtype N_Unary_Op is SN.N_Unary_Op;

   subtype N_Assignment_Statement_Id is SN.N_Assignment_Statement_Id;
   subtype N_Attribute_Reference_Id is SN.N_Attribute_Reference_Id;
   subtype N_Block_Statement_Id is SN.N_Block_Statement_Id;
   subtype N_Component_Association_Id is SN.N_Component_Association_Id;
   subtype N_Continue_Statement_Id is SN.N_Continue_Statement_Id;
   subtype N_Exit_Statement_Id is SN.N_Exit_Statement_Id;
   subtype N_Function_Call_Id is SN.N_Function_Call_Id;
   subtype N_Has_Chars is SN.N_Has_Chars;
   subtype N_Iteration_Scheme_Id is SN.N_Iteration_Scheme_Id;
   subtype N_Loop_Statement_Id is SN.N_Loop_Statement_Id;
   subtype N_Membership_Test_Id is SN.N_Membership_Test_Id;
   subtype N_Object_Declaration_Id is SN.N_Object_Declaration_Id;
   subtype N_Op_Id is SN.N_Op_Id;
   subtype N_Package_Body_Id is SN.N_Package_Body_Id;
   subtype N_Package_Specification_Id is SN.N_Package_Specification_Id;
   subtype N_Pragma_Id is SN.N_Pragma_Id;
   subtype N_Quantified_Expression_Id is SN.N_Quantified_Expression_Id;
   subtype N_Slice_Id is SN.N_Slice_Id;
   subtype N_String_Literal_Id is SN.N_String_Literal_Id;
   subtype N_Subexpr_Id is SN.N_Subexpr_Id;

   subtype Opt_N_Attribute_Reference_Id is SN.Opt_N_Attribute_Reference_Id;
   subtype Opt_N_Block_Statement_Id is SN.Opt_N_Block_Statement_Id;
   subtype Opt_N_Case_Statement_Alternative_Id is
     SN.Opt_N_Case_Statement_Alternative_Id;
   subtype Opt_N_Component_Association_Id is SN.Opt_N_Component_Association_Id;
   subtype Opt_N_Declaration_Id is SN.Opt_N_Declaration_Id;
   subtype Opt_N_Exit_Statement_Id is SN.Opt_N_Exit_Statement_Id;
   subtype Opt_N_Identifier_Id is SN.Opt_N_Identifier_Id;
   subtype Opt_N_Iteration_Scheme_Id is SN.Opt_N_Iteration_Scheme_Id;
   subtype Opt_N_Loop_Parameter_Specification_Id is
     SN.Opt_N_Loop_Parameter_Specification_Id;
   subtype Opt_N_Loop_Statement_Id is SN.Opt_N_Loop_Statement_Id;
   subtype Opt_N_Object_Declaration_Id is SN.Opt_N_Object_Declaration_Id;
   subtype Opt_N_Pragma_Argument_Association_Id is
     SN.Opt_N_Pragma_Argument_Association_Id;
   subtype Opt_N_Op_Id is SN.Opt_N_Op_Id;
   subtype Opt_N_Package_Body_Id is SN.Opt_N_Package_Body_Id;
   subtype Opt_N_Package_Specification_Id is SN.Opt_N_Package_Specification_Id;
   subtype Opt_N_Pragma_Id is SN.Opt_N_Pragma_Id;
   subtype Opt_N_Subexpr_Id is SN.Opt_N_Subexpr_Id;

   N_Abstract_Subprogram_Declaration : Node_Kind renames
     SN.N_Abstract_Subprogram_Declaration;
   N_Aggregate                       : Node_Kind renames SN.N_Aggregate;
   N_Allocator                       : Node_Kind renames SN.N_Allocator;
   N_And_Then                        : Node_Kind renames SN.N_And_Then;
   N_Assignment_Statement            : Node_Kind renames
     SN.N_Assignment_Statement;
   N_Attribute_Reference             : Node_Kind renames
     SN.N_Attribute_Reference;
   N_Block_Statement                 : Node_Kind renames SN.N_Block_Statement;
   N_Case_Expression                 : Node_Kind renames SN.N_Case_Expression;
   N_Case_Expression_Alternative     : Node_Kind renames
     SN.N_Case_Expression_Alternative;
   N_Case_Statement                  : Node_Kind renames SN.N_Case_Statement;
   N_Case_Statement_Alternative      : Node_Kind renames
     SN.N_Case_Statement_Alternative;
   N_Character_Literal               : Node_Kind renames
     SN.N_Character_Literal;
   N_Component_Association           : Node_Kind renames
     SN.N_Component_Association;
   N_Component_Declaration           : Node_Kind renames
     SN.N_Component_Declaration;
   N_Defining_Identifier             : Node_Kind renames
     SN.N_Defining_Identifier;
   N_Defining_Operator_Symbol        : Node_Kind renames
     SN.N_Defining_Operator_Symbol;
   N_Delta_Aggregate                 : Node_Kind renames SN.N_Delta_Aggregate;
   N_Derived_Type_Definition         : Node_Kind renames
     SN.N_Derived_Type_Definition;
   N_Elsif_Part                      : Node_Kind renames SN.N_Elsif_Part;
   N_Entry_Call_Statement            : Node_Kind renames
     SN.N_Entry_Call_Statement;
   N_Entry_Declaration               : Node_Kind renames
     SN.N_Entry_Declaration;
   N_Exception_Handler               : Node_Kind renames
     SN.N_Exception_Handler;
   N_Exit_Statement                  : Node_Kind renames SN.N_Exit_Statement;
   N_Continue_Statement              : Node_Kind renames
     SN.N_Continue_Statement;
   N_Explicit_Dereference            : Node_Kind renames
     SN.N_Explicit_Dereference;
   N_Expression_With_Actions         : Node_Kind renames
     SN.N_Expression_With_Actions;
   N_Extended_Return_Statement       : Node_Kind renames
     SN.N_Extended_Return_Statement;
   N_Full_Type_Declaration           : Node_Kind renames
     SN.N_Full_Type_Declaration;
   N_Expanded_Name                   : Node_Kind renames SN.N_Expanded_Name;
   N_Extension_Aggregate             : Node_Kind renames
     SN.N_Extension_Aggregate;
   N_Function_Call                   : Node_Kind renames SN.N_Function_Call;
   N_Goto_Statement                  : Node_Kind renames SN.N_Goto_Statement;
   N_Handled_Sequence_Of_Statements  : Node_Kind renames
     SN.N_Handled_Sequence_Of_Statements;
   N_Identifier                      : Node_Kind renames SN.N_Identifier;
   N_If_Expression                   : Node_Kind renames SN.N_If_Expression;
   N_If_Statement                    : Node_Kind renames SN.N_If_Statement;
   N_In                              : Node_Kind renames SN.N_In;
   N_Indexed_Component               : Node_Kind renames
     SN.N_Indexed_Component;
   N_Integer_Literal                 : Node_Kind renames SN.N_Integer_Literal;
   N_Iterated_Component_Association  : Node_Kind renames
     SN.N_Iterated_Component_Association;
   N_Itype_Reference                 : Node_Kind renames SN.N_Itype_Reference;
   N_Label                           : Node_Kind renames SN.N_Label;
   N_Loop_Statement                  : Node_Kind renames SN.N_Loop_Statement;
   N_Not_In                          : Node_Kind renames SN.N_Not_In;
   N_Null                            : Node_Kind renames SN.N_Null;
   N_Object_Declaration              : Node_Kind renames
     SN.N_Object_Declaration;
   N_Object_Renaming_Declaration     : Node_Kind renames
     SN.N_Object_Renaming_Declaration;
   N_Op_Abs                          : Node_Kind renames SN.N_Op_Abs;
   N_Op_Add                          : Node_Kind renames SN.N_Op_Add;
   N_Op_And                          : Node_Kind renames SN.N_Op_And;
   N_Op_Concat                       : Node_Kind renames SN.N_Op_Concat;
   N_Op_Divide                       : Node_Kind renames SN.N_Op_Divide;
   N_Op_Eq                           : Node_Kind renames SN.N_Op_Eq;
   N_Op_Expon                        : Node_Kind renames SN.N_Op_Expon;
   N_Op_Ge                           : Node_Kind renames SN.N_Op_Ge;
   N_Op_Gt                           : Node_Kind renames SN.N_Op_Gt;
   N_Op_Le                           : Node_Kind renames SN.N_Op_Le;
   N_Op_Lt                           : Node_Kind renames SN.N_Op_Lt;
   N_Op_Mod                          : Node_Kind renames SN.N_Op_Mod;
   N_Op_Multiply                     : Node_Kind renames SN.N_Op_Multiply;
   N_Op_Or                           : Node_Kind renames SN.N_Op_Or;
   N_Op_Minus                        : Node_Kind renames SN.N_Op_Minus;
   N_Op_Ne                           : Node_Kind renames SN.N_Op_Ne;
   N_Op_Not                          : Node_Kind renames SN.N_Op_Not;
   N_Op_Plus                         : Node_Kind renames SN.N_Op_Plus;
   N_Op_Rem                          : Node_Kind renames SN.N_Op_Rem;
   N_Op_Rotate_Left                  : Node_Kind renames SN.N_Op_Rotate_Left;
   N_Op_Rotate_Right                 : Node_Kind renames SN.N_Op_Rotate_Right;
   N_Op_Shift_Left                   : Node_Kind renames SN.N_Op_Shift_Left;
   N_Op_Shift_Right                  : Node_Kind renames SN.N_Op_Shift_Right;
   N_Op_Shift_Right_Arithmetic       : Node_Kind renames
     SN.N_Op_Shift_Right_Arithmetic;
   N_Op_Subtract                     : Node_Kind renames SN.N_Op_Subtract;
   N_Op_Xor                          : Node_Kind renames SN.N_Op_Xor;
   N_Or_Else                         : Node_Kind renames SN.N_Or_Else;
   N_Others_Choice                   : Node_Kind renames SN.N_Others_Choice;
   N_Package_Body                    : Node_Kind renames SN.N_Package_Body;
   N_Package_Declaration             : Node_Kind renames
     SN.N_Package_Declaration;
   N_Private_Extension_Declaration   : Node_Kind renames
     SN.N_Private_Extension_Declaration;
   N_Private_Type_Declaration        : Node_Kind renames
     SN.N_Private_Type_Declaration;
   N_Procedure_Call_Statement        : Node_Kind renames
     SN.N_Procedure_Call_Statement;
   N_Protected_Body                  : Node_Kind renames SN.N_Protected_Body;
   N_Protected_Type_Declaration      : Node_Kind renames
     SN.N_Protected_Type_Declaration;
   N_Pragma                          : Node_Kind renames SN.N_Pragma;
   N_Qualified_Expression            : Node_Kind renames
     SN.N_Qualified_Expression;
   N_Quantified_Expression           : Node_Kind renames
     SN.N_Quantified_Expression;
   N_Real_Literal                    : Node_Kind renames SN.N_Real_Literal;
   N_Raise_Expression                : Node_Kind renames SN.N_Raise_Expression;
   N_Raise_Statement                 : Node_Kind renames SN.N_Raise_Statement;
   N_Range                           : Node_Kind renames SN.N_Range;
   N_Selected_Component              : Node_Kind renames
     SN.N_Selected_Component;
   N_Simple_Return_Statement         : Node_Kind renames
     SN.N_Simple_Return_Statement;
   N_Slice                           : Node_Kind renames SN.N_Slice;
   N_String_Literal                  : Node_Kind renames SN.N_String_Literal;
   N_Subprogram_Declaration          : Node_Kind renames
     SN.N_Subprogram_Declaration;
   N_Subprogram_Body                 : Node_Kind renames SN.N_Subprogram_Body;
   N_Subtype_Declaration             : Node_Kind renames
     SN.N_Subtype_Declaration;
   N_Subtype_Indication              : Node_Kind renames
     SN.N_Subtype_Indication;
   N_Target_Name                     : Node_Kind renames SN.N_Target_Name;
   N_Task_Type_Declaration           : Node_Kind renames
     SN.N_Task_Type_Declaration;
   N_Task_Body                       : Node_Kind renames SN.N_Task_Body;
   N_Type_Conversion                 : Node_Kind renames SN.N_Type_Conversion;
   N_Unchecked_Type_Conversion       : Node_Kind renames
     SN.N_Unchecked_Type_Conversion;
   N_With_Clause                     : Node_Kind renames SN.N_With_Clause;

   Current_Error_Node : Node_Id renames Atree.Current_Error_Node;

   function "=" (L, R : Node_Kind) return Boolean renames SN."=";

   function Comes_From_Source (N : Node_Id) return Boolean
   renames SN.Comes_From_Source;

   function Enclosing_Comp_Unit_Node (N : Node_Id) return Node_Id
   with
     Post =>
       No (Enclosing_Comp_Unit_Node'Result)
       or else Nkind (Enclosing_Comp_Unit_Node'Result) = N_Compilation_Unit;

   function End_Location (N : Node_Id) return Source_Ptr
   renames Sinfo.Utils.End_Location;

   function Is_Rewrite_Substitution (N : Node_Id) return Boolean
   renames Atree.Is_Rewrite_Substitution;
   --  ??? As for Original_Node.

   function Nkind (N : Node_Id) return Node_Kind renames SN.Nkind;

   function No (N : Node_Id) return Boolean renames Atree.No;

   function Original_Node (N : Node_Id) return Node_Id
   renames Atree.Original_Node;
   --  ??? If possible, it would be better to remove occurrences of this by
   --  including it in other querries (Comes_From_Source?) when required.

   function Present (N : Node_Id) return Boolean renames Atree.Present;

   function Sloc (N : Node_Id) return Source_Ptr renames SN.Sloc;

   ---------------------------
   --  Abstract Syntax Tree --
   ---------------------------

   function Actions (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N)
       in N_And_Then
        | N_Case_Expression_Alternative
        | N_Compilation_Unit_Aux
        | N_Compound_Statement
        | N_Expression_With_Actions
        | N_Or_Else;

   function Aggregate_Bounds (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Aggregate;

   function All_Present (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Quantified_Expression;

   function Alternatives (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N) in N_Case_Expression | N_Case_Statement | N_In | N_Not_In;

   function Ancestor_Part (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Extension_Aggregate;

   function Attribute_Constrained_Static_Value (N : Node_Id) return Boolean
   with Pre => SPARK_Util.Attr_Constrained_Statically_Known (N);

   function Attribute_Name (N : Node_Id) return Name_Id
   with Pre => Nkind (N) = N_Attribute_Reference;

   function Box_Present (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N)
       in N_Component_Association
        | N_Formal_Abstract_Subprogram_Declaration
        | N_Formal_Concrete_Subprogram_Declaration
        | N_Formal_Package_Declaration
        | N_Generic_Association
        | N_Iterated_Component_Association;

   function Char_Literal_Value (N : Node_Id) return Uint
   with Pre => Nkind (N) = N_Character_Literal;

   function Chars (N : Node_Id) return Name_Id
   with Pre => Nkind (N) in SN.N_Has_Chars;

   function Choice_List (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N) in N_Component_Association | N_Iterated_Component_Association;

   function Component_Associations (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N) in N_Aggregate | N_Delta_Aggregate | N_Extension_Aggregate;

   function Component_Definition (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Component_Declaration;

   function Component_Subtype_Indication (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Full_Type_Declaration | N_Subtype_Declaration;
   --  Return the subtype indication associated to the component type of an
   --  array type declaration.

   function Condition (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Continue_Statement
        | N_Elsif_Part
        | N_Exit_Statement
        | N_If_Statement
        | N_Iteration_Scheme
        | N_Quantified_Expression
        | N_Raise_xxx_Error;

   function Condition_Actions (N : Node_Id) return List_Id
   with Pre => Nkind (N) in N_Elsif_Part | N_Iteration_Scheme;

   function Context_Items (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_Compilation_Unit;

   function Controlling_Argument (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Subprogram_Call;

   function Corresponding_Integer_Value (N : Node_Id) return Uint
   with Pre => Nkind (N) = N_Real_Literal;

   function Declarations (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N)
       in N_Accept_Statement
        | N_Block_Statement
        | N_Compilation_Unit_Aux
        | N_Entry_Body
        | N_Package_Body
        | N_Protected_Body
        | N_Subprogram_Body
        | N_Task_Body;

   function Depends_On_Discriminant (N : Node_Id) return Boolean;

   function Defining_Identifier (N : Node_Id) return Entity_Id
   renames SN.Defining_Identifier;

   function Discrete_Choices (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N)
       in N_Case_Expression_Alternative
        | N_Case_Statement_Alternative
        | N_Iterated_Component_Association
        | N_Variant;

   function Discrete_Range (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Slice;

   function Discrete_Subtype_Definition (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Entry_Declaration
        | N_Entry_Index_Specification
        | N_Loop_Parameter_Specification;

   function Do_Check_On_Scalar_Conversion (N : Node_Id) return Boolean
   with Pre => Nkind (N) in SN.N_Subexpr;
   --  Return True if a check is needed on an expression which requires a
   --  scalar conversion. The check may be either a range check, an index
   --  check, or an overflow check.

   function Do_Division_Check (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Op_Divide | N_Op_Mod | N_Op_Rem;

   function Do_Overflow_Check (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N)
       in N_Op
        | N_Attribute_Reference
        | N_Case_Expression
        | N_If_Expression
        | N_Type_Conversion;

   function Do_Range_Check (N : Node_Id) return Boolean
   with Pre => Nkind (N) in SN.N_Subexpr;

   function Else_Actions (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_If_Expression;

   function Else_Statements (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_If_Statement;

   function Elsif_Parts (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_If_Statement;

   function Enclosing_Statement (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Elsif_Part
        | N_Case_Statement_Alternative
        | N_Exception_Handler
        | N_Function_Call;
   --  Renaming of Parent for parts of conditional statements, handlers and
   --  calls to functions with side-effects.

   function Entity (N : Node_Id) return Entity_Id
   with
     Pre =>
       Nkind (N)
       in N_Has_Entity
        | N_Aspect_Specification
        | N_Attribute_Definition_Clause;

   function Entry_Body_Barrier (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Entry_Body;
   --  Return the condition of the entry formal part of N

   function Etype (N : Node_Id) return Entity_Id
   with Pre => Nkind (N) in SN.N_Has_Etype;

   function Exception_Choices
     (N : Sinfo.Nodes.N_Exception_Handler_Id) return List_Id
   renames Sinfo.Nodes.Exception_Choices;

   function Exception_Handlers
     (N : Sinfo.Nodes.N_Handled_Sequence_Of_Statements_Id) return List_Id
   renames Sinfo.Nodes.Exception_Handlers;

   function Expression (N : Node_Id) return Node_Id
   with
     Post =>
       No (Expression'Result)
       or else Nkind (Expression'Result) in N_Subexpr | N_Subtype_Indication;

   function Expression_Contains_Old_Or_Loop_Entry
     (Expr : Node_Id) return Boolean
   with Pre => Nkind (Expr) in N_Subexpr;
   --  Traverse expression to find references to Old and Loop_Entry attributes

   function Expression_Contains_Primitives_Calls_Of
     (Expr : Node_Id; Typ : Entity_Id) return Boolean
   renames Exp_Util.Expression_Contains_Primitives_Calls_Of;

   function Expressions (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N)
       in N_Aggregate
        | N_Attribute_Reference
        | N_Extension_Aggregate
        | N_If_Expression
        | N_Indexed_Component;

   function First_Actual (Node : Node_Id) return Node_Id
   renames Sem_Util.First_Actual;

   function Finally_Statements
     (N : Sinfo.Nodes.N_Handled_Sequence_Of_Statements_Id) return List_Id
   renames Sinfo.Nodes.Finally_Statements;

   function From_Aspect_Specification (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Pragma;

   function Get_Address_Expr (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Subprogram_Declaration | N_Object_Declaration;
   --  Return the expression associated to the address representation item for
   --  the defining entity of the declaration N if any.

   function Get_Called_Entity (N : Node_Id) return Entity_Id
   with
     Pre  => Nkind (N) in N_Subprogram_Call | N_Entry_Call_Statement | N_Op,
     Post =>
       (if Nkind (N) in N_Op
        then Einfo.Entities.Is_Intrinsic_Subprogram (Get_Called_Entity'Result)
        else
          Get_Called_Entity'Result
          = Sem_Aux.Ultimate_Alias (Get_Called_Entity'Result));
   --  Same as Sem_Aux.Get_Called_Entity except that, on intrinsic operators,
   --  it returns the associated function instead of the operator name.

   function Get_Entire_Object (N : Node_Id) return Entity_Id
   with Pre => Nkind (N) in N_Subexpr;
   --  Similar to Sem_Util.Get_Enclosing_Object except that it does not
   --  return Empty on dereferences of access objects.
   --  It can only return Empty when called on expressions which are not paths.

   function Get_Pragma_Id (N : Node_Id) return Pragma_Id
   with Pre => Nkind (N) = N_Pragma;

   function Get_Range_Check_Info
     (N : Node_Id) return SPARK_Util.Scalar_Check_Kind
   with
     Pre => Nkind (N) in N_Subexpr and then Do_Check_On_Scalar_Conversion (N);
   --  @param N a scalar expression requiring a check
   --  @return Check_Kind the kind of check expected
   --     (overflow, range, index...).

   function Get_Return_Object (N : Node_Id) return Entity_Id
   with Pre => Nkind (N) = N_Extended_Return_Statement;

   function Has_Inferable_Discriminants (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;

   function Has_Target_Names (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Assignment_Statement;

   function Handled_Statement_Sequence (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Accept_Statement
        | N_Block_Statement
        | N_Entry_Body
        | N_Extended_Return_Statement
        | N_Package_Body
        | N_Subprogram_Body
        | N_Task_Body;

   function Has_Wide_Character (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_String_Literal;

   function Has_Wide_Wide_Character (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_String_Literal;

   function High_Bound (N : Node_Id) return Node_Id
   with
     Pre  =>
       Nkind (N)
       in N_Range
        | N_Real_Range_Specification
        | N_Signed_Integer_Type_Definition,
     Post => Nkind (High_Bound'Result) in N_Subexpr;

   function Identifier (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Aspect_Specification
        | N_At_Clause
        | N_Block_Statement
        | N_Designator
        | N_Enumeration_Representation_Clause
        | N_Loop_Statement
        | N_Record_Representation_Clause
        | N_Label;

   function Inherited_Discriminant (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Component_Association;

   function Intval (N : Node_Id) return Uint
   with Pre => Nkind (N) = N_Integer_Literal;

   function Is_Choice_Of_Unconstrained_Array_Update
     (N : Node_Id) return Boolean;
   --  Determines whether the node is some kind of a choice of a 'Update of
   --  an unconstrained array. This is useful for producing the extra
   --  checks required for updates of unconstrained arrays.

   function Is_Component_Left_Opnd (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Op_Concat;

   function Is_Component_Right_Opnd (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Op_Concat;

   function Is_Controlling_Actual (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;

   function Is_Container_Aggregate (Exp : Node_Id) return Boolean
   renames Sem_Util.Is_Container_Aggregate;
   --  Make the frontend routine to units that only use SPARK wrappers to
   --  access the GNAT AST.

   function Is_Iterator_Over_Array (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Iterator_Specification;

   function Is_Null_Aggregate (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N) in N_Aggregate | N_Extension_Aggregate | N_Delta_Aggregate;

   function Is_Rewritten_Op_Eq (N : Node_Id) return Boolean;
   --  Return true if N is a function call and its original node is an equality
   --  operation. This is used to handle specifically dispatching calls to
   --  primitive equality.

   function Is_Root_Prefix_Of_Deep_Choice (N : Node_Id) return Boolean
   renames Sem_Aggr.Is_Root_Prefix_Of_Deep_Choice;

   function Is_Tag_Indeterminate (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;

   function Is_Type_Renaming (Decl : Node_Id) return Boolean
   with Pre => Nkind (Decl) in N_Subtype_Declaration | N_Full_Type_Declaration;
   --  Returns whether type declaration Decl defines a new name for an
   --  existing type, either through a subtype:
   --     subtype Sub is Existing;
   --  or a derived type:
   --     type Der is new Existing;

   function Is_Variable (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;
   --  Renaming of Sem_Util.Is_Variable with default value for
   --  Use_Original_Node. This function should not be used on formal
   --  parameters (see comment in Sem_Util).

   generic procedure Iterate_Call_Parameters
   renames Sem_Util.Iterate_Call_Parameters;

   function Iteration_Scheme (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Loop_Statement;

   function Iterator_Filter (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N) in N_Iterator_Specification | N_Loop_Parameter_Specification;

   function Iterator_Specification (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Iteration_Scheme | N_Quantified_Expression;

   function Itype (N : Node_Id) return Entity_Id
   with Pre => Nkind (N) = N_Itype_Reference;

   function Left_Opnd (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N) in N_And_Then | N_In | N_Not_In | N_Or_Else | N_Binary_Op;

   function Library_Unit (N : Node_Id) return Node_Id
   with
     Pre  => Nkind (N) in N_Compilation_Unit | N_With_Clause,
     Post => Nkind (Library_Unit'Result) = N_Compilation_Unit;

   function Limited_Present (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_With_Clause;

   function Loop_Actions (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_Iterated_Component_Association;

   function Loop_Parameter_Specification (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Iteration_Scheme | N_Quantified_Expression;

   function Low_Bound (N : Node_Id) return Node_Id
   with
     Pre  =>
       Nkind (N)
       in N_Range
        | N_Real_Range_Specification
        | N_Signed_Integer_Type_Definition,
     Post => Nkind (Low_Bound'Result) in N_Subexpr;

   function Name (N : Node_Id) return Node_Id;

   function Next_Actual (Actual_Id : Node_Id) return Node_Id
   renames Sem_Util.Next_Actual;

   function Of_Present (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Iterator_Specification;

   function Pragma_Argument_Associations (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_Pragma;

   function Pragma_Identifier (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Pragma;

   function Prefix (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Attribute_Reference
        | N_Expanded_Name
        | N_Explicit_Dereference
        | N_Indexed_Component
        | N_Reference
        | N_Selected_Component
        | N_Slice;

   function Realval (N : Node_Id) return Ureal
   with Pre => Nkind (N) = N_Real_Literal;

   function Reason (N : Node_Id) return Uint
   with Pre => Nkind (N) in N_Raise_xxx_Error;

   function Return_Object_Declarations (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_Extended_Return_Statement;

   function Return_Statement_Entity (N : Node_Id) return Entity_Id
   with
     Pre =>
       Nkind (N) in N_Extended_Return_Statement | N_Simple_Return_Statement;

   function Reverse_Present (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N) in N_Iterator_Specification | N_Loop_Parameter_Specification;

   function Right_Opnd (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Op | N_And_Then | N_In | N_Not_In | N_Or_Else;

   function Selector_Name (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Expanded_Name
        | N_Generic_Association
        | N_Parameter_Association
        | N_Selected_Component;

   function Statements (N : Node_Id) return List_Id
   with
     Pre =>
       Nkind (N)
       in N_Abortable_Part
        | N_Accept_Alternative
        | N_Case_Statement_Alternative
        | N_Delay_Alternative
        | N_Entry_Call_Alternative
        | N_Exception_Handler
        | N_Handled_Sequence_Of_Statements
        | N_Loop_Statement
        | N_Triggering_Alternative;

   function Strval (N : Node_Id) return String_Id
   with Pre => Nkind (N) in N_Operator_Symbol | N_String_Literal;

   function Subtype_Indication (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Access_To_Object_Definition
        | N_Component_Definition
        | N_Derived_Type_Definition
        | N_Iterator_Specification
        | N_Private_Extension_Declaration
        | N_Subtype_Declaration;

   function Subtype_Mark (N : Node_Id) return Node_Id
   with
     Pre =>
       Nkind (N)
       in N_Access_Definition
        | N_Formal_Derived_Type_Definition
        | N_Formal_Object_Declaration
        | N_Object_Renaming_Declaration
        | N_Qualified_Expression
        | N_Subtype_Indication
        | N_Type_Conversion
        | N_Unchecked_Type_Conversion
        | N_Use_Type_Clause;

   function Then_Actions (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_If_Expression;

   function Then_Statements (N : Node_Id) return List_Id
   with Pre => Nkind (N) in N_Elsif_Part | N_If_Statement;

   function Type_Definition (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Full_Type_Declaration;

   function Unique_Defining_Entity (N : Node_Id) return Entity_Id
   renames Sem_Util.Unique_Defining_Entity;

   function Unqual_Conv (N : Node_Id) return Node_Id
   with Pre => Nkind (N) in N_Has_Etype;

   function Unit (N : Node_Id) return Node_Id
   with Pre => Nkind (N) = N_Compilation_Unit;

   function Variants (N : Node_Id) return List_Id
   with Pre => Nkind (N) = N_Variant_Part;

   generic
      with function Process (N : Node_Id) return Atree.Traverse_Result is <>;
   procedure Traverse_More_Proc (Node : Node_Id);
   pragma Inline (Traverse_More_Proc);
   --  Renames Sem_Util.Traverse_More_Proc

   -----------------------
   -- Static Evaluation --
   -----------------------

   function Compile_Time_Known_Value (N : Node_Id) return Boolean
   renames Sem_Eval.Compile_Time_Known_Value;

   function Compile_Time_Known_Bounds (T : Entity_Id) return Boolean
   renames Sem_Eval.Compile_Time_Known_Bounds;

   function Expr_Value (N : Node_Id) return Uint
   with Pre => Compile_Time_Known_Value (N);

   function Expr_Value_R (N : Node_Id) return Ureal
   with Pre => Compile_Time_Known_Value (N);

   function Is_True (U : Opt_Ubool) return Boolean renames Sem_Util.Is_True;

   function Is_OK_Static_Expression (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;

   function Is_OK_Static_Range (N : Node_Id) return Boolean
   with
     Pre =>
       Nkind (N)
       in N_Range
        | N_Real_Range_Specification
        | N_Signed_Integer_Type_Definition;

   function Is_In_Range (N : Node_Id; Typ : Entity_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr and then Is_Static_Expression (N);
   --  Calls Sem_Eval.Is_In_Range with Assume_Valid set to True.

   function Is_Static_Expression (N : Node_Id) return Boolean
   with Pre => Nkind (N) in N_Subexpr;

end SPARK_Atree;
