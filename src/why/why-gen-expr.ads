------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - E X P R                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2022, AdaCore                     --
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

with GNATCOLL.Symbols;          use GNATCOLL.Symbols;
with Gnat2Why.Util;             use Gnat2Why.Util;
with Snames;                    use Snames;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Atree.Entities;      use SPARK_Atree.Entities;
with SPARK_Util;                use SPARK_Util;
with Types;                     use Types;
with Uintp;                     use Uintp;
with VC_Kinds;                  use VC_Kinds;
with Why.Atree.Builders;        use Why.Atree.Builders;
with Why.Conversions;           use Why.Conversions;
with Why.Ids;                   use Why.Ids;
with Why.Inter;                 use Why.Inter;
with Why.Sinfo;                 use Why.Sinfo;
with Why.Types;                 use Why.Types;

package Why.Gen.Expr is

   procedure Initialize_Tables_Nth_Roots;
   --  This initializing procedure is called after initializing the module
   --  Uintp to fill in the tabled values for nth roots of the modulus of
   --  machine integers, and check in ghost code that the tabled values are
   --  correct.

   function Is_False_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "false"

   function Is_True_Boolean (P : W_Expr_Id) return Boolean;
   --  Check if the given program is the program "true"

   function Is_Essentially_Void (W : W_Prog_Id) return Boolean;
   --  Check if the given program is "void" or similarly effectless (label
   --  nodes).

   function Is_Void (W : W_Prog_Id) return Boolean;

   function Bool_True (D : EW_Domain) return W_Expr_Id is
     (New_Literal (Value => EW_True, Domain => D));
   function Bool_False (D : EW_Domain) return W_Expr_Id is
     (New_Literal (Value => EW_False, Domain => D));

   function Pred_Of_Boolean_Term (W : W_Term_Id) return W_Pred_Id;
   --  @param W a Why3 term expression
   --  @return the equivalent Why3 pred expression

   function Boolean_Expr_Of_Pred
     (W      : W_Pred_Id;
      Domain : EW_Domain)
      return W_Expr_Id;
   --  @param W a Why3 pred expression
   --  @param Domain translation domain
   --  @return the equivalent Why3 expression, depending on the [Domain]

   function Boolean_Prog_Of_Pred (W : W_Pred_Id) return W_Prog_Id;
   --  @param W a Why3 pred expression
   --  @return the equivalent Why3 prog expression

   function Boolean_Term_Of_Pred (W : W_Pred_Id) return W_Term_Id;
   --  @param W a Why3 pred expression
   --  @return the equivalent Why3 term expression

   function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean;
   --  Check whether a conversion between those types might require sliding

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain)
       return W_Expr_Id;

   function New_And_Prog (Left, Right : W_Prog_Id) return W_Prog_Id is
      (+New_And_Expr (+Left, +Right, EW_Prog));

   function New_And_Term (Left, Right : W_Term_Id) return W_Term_Id is
      (+New_And_Expr (+Left, +Right, EW_Term));

   function New_And_Pred (Left, Right : W_Pred_Id) return W_Pred_Id is
      (+New_And_Expr (+Left, +Right, EW_Pred));

   function New_And_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id)
       return W_Expr_Id;
   --  Generate the expression "Left and Right"; choose the right "and"
   --  operation depending on "Base", e.g. for modular or boolean types.

   function New_And_Pred (Conjuncts : W_Pred_Array) return W_Pred_Id;

   function New_And_Then_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain)
       return W_Expr_Id;

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id;

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Prog_Id)
      return W_Prog_Id
   is (+W_Expr_Id'(New_Comparison (Symbol, +Left, +Right, EW_Prog)));

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Term_Id)
      return W_Term_Id
   is (+W_Expr_Id'(New_Comparison (Symbol, +Left, +Right, EW_Term)));

   function New_Comparison
     (Symbol      : W_Identifier_Id;
      Left, Right : W_Term_Id)
      return W_Pred_Id
   is (+W_Expr_Id'(New_Comparison (Symbol, +Left, +Right, EW_Pred)));

   function New_Counterexample_Assign
     (If_Node   : Node_Id;
      Condition : W_Prog_Id)
      return W_Prog_Id;
   --  This takes a condition of an if-statement (or case-statement)
   --  [Condition] and builds an assignment to a variable spark__branch with
   --  label [If_Node], which is then dereferenced to yield the value of the
   --  condition.
   --  [Condition] becomes
   --  [spark__branch.bool__content <- Condition;
   --  ("node_id:If_Node" spark__branch).bool__content]

   function New_Ada_Equality
     (Typ         : Type_Kind_Id;
      Domain      : EW_Domain;
      Left, Right : W_Expr_Id)
      return W_Expr_Id;
   --  Generate a boolean term which expresses the translation of "Left =
   --  Right" in Ada semantics, where the equality is the one of type Typ.
   --  If the type has a user-provided primitive equality and if its most
   --  underlying type is a record type or is limited, use the user-provided
   --  equality. Else, use the predefined equality.

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id;

   function New_Or_Term (Left, Right : W_Term_Id) return W_Term_Id is
     (+New_Or_Expr (+Left, +Right, EW_Term));

   function New_Or_Pred (Left, Right : W_Pred_Id) return W_Pred_Id is
     (+New_Or_Expr (+Left, +Right, EW_Pred));

   function New_Or_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain;
      Base        : W_Type_Id)
      return W_Expr_Id;
   --  Generate the expression "Left or Right"; choose the right "or" operation
   --  depending on "Base", e.g. for modular or boolean types.

   function New_Or_Pred (Conjuncts : W_Pred_Array) return W_Pred_Id;

   function New_Or_Else_Expr
     (Left, Right : W_Expr_Id;
      Domain      : EW_Domain)
      return W_Expr_Id;

   function New_Xor_Expr
      (Left, Right : W_Expr_Id;
       Domain      : EW_Domain;
       Base        : W_Type_Id)
       return W_Expr_Id;
   --  Build an expression "Left xor Right", and choose the right xor operation
   --  depending on "Base", which is either EW_Bool_Type or EW_Int_Type.

   function Why_Default_Value
     (Domain : EW_Domain;
      E      : Type_Kind_Id)
      return W_Expr_Id;
   --  Return the default value for a given type

   function New_Simpl_Conditional
     (Condition : W_Expr_Id;
      Then_Part : W_Expr_Id;
      Else_Part : W_Expr_Id;
      Domain    : EW_Domain)
      return W_Expr_Id;
   --  Conditional, simplify if condition is true/false.

   function New_Simpl_Conditional
     (Condition : W_Prog_Id;
      Then_Part : W_Prog_Id;
      Else_Part : W_Prog_Id)
      return W_Prog_Id
   is (+W_Expr_Id'
         (New_Simpl_Conditional
            (+Condition, +Then_Part, +Else_Part, EW_Prog)));

   function New_Simpl_Conditional
     (Condition : W_Pred_Id;
      Then_Part : W_Pred_Id;
      Else_Part : W_Pred_Id)
      return W_Pred_Id
   is (+W_Expr_Id'
         (New_Simpl_Conditional
            (+Condition, +Then_Part, +Else_Part, EW_Pred)));

   function New_Shape_Label (Node : Node_Id) return Symbol;
   --  Return a label representing the shape of the Ada code surrounding the
   --  input node. This label is used to name the VC file for manual proof.

   function New_Comment_Label
     (Node   : Node_Id;
      Loc    : Symbol;
      Reason : VC_Kind)
      return Symbol;
   --  Return a label with the tag "comment" in order to display VC information
   --  in VC generated files.

   function New_Sub_VC_Marker (N : Node_Id) return Symbol;
   --  Return a label that contains the pretty printing for the given node

   function New_Function_Call
     (Ada_Node : Node_Id := Empty;
      Subp     : Node_Id;
      Selector : Selection_Kind := Why.Inter.Standard;
      Name     : W_Identifier_Id;
      Args     : W_Expr_Array;
      Check    : Boolean;
      Domain   : EW_Domain;
      Typ      : W_Type_Id) return W_Expr_Id
   with Pre => (if Check then Domain = EW_Prog);
   --  If Check is True, build a call to Name(Args) with VC and location
   --  labels. Otherwise, build a call in the appropriate domain. In the
   --  term or pred domain, use an epsilon or a direct call as appropriate.

   function New_Operator_Call
      (Ada_Node   : Node_Id;
       Name       : W_Identifier_Id;
       Fix_Name   : Boolean := False;
       Args       : W_Expr_Array;
       Reason     : VC_Kind;
       Check      : Boolean;
       Domain     : EW_Domain;
       Typ        : W_Type_Id;
       Check_Info : Check_Info_Type := New_Check_Info)
       return W_Expr_Id
   with
     Pre => (if Check then Domain = EW_Prog);
   --  If Check is True, build a call to Name(Progs) using New_VC_Call. When
   --  Fix_Name is True, adjust Name to the program space. Otherwise, build a
   --  call in the appropriate domain.

   function New_VC_Call
      (Ada_Node   : Node_Id;
       Name       : W_Identifier_Id;
       Progs      : W_Expr_Array;
       Reason     : VC_Kind;
       Typ        : W_Type_Id;
       Check_Info : Check_Info_Type := New_Check_Info)
       return W_Prog_Id;
   --  Build a call to Name(Progs) with VC and location labels

   function New_VC_Expr
     (Ada_Node   : Node_Id;
      Expr       : W_Expr_Id;
      Reason     : VC_Kind;
      Domain     : EW_Domain;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Expr_Id
   with Pre => Present (Ada_Node) and then Domain /= EW_Term;
   --  Put VC and location labels on the expression

   function New_VC_Pred
     (Ada_Node   : Node_Id;
      Expr       : W_Pred_Id;
      Reason     : VC_Kind;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Pred_Id
   is (+New_VC_Expr (Ada_Node, +Expr, Reason, EW_Pred, Check_Info));

   function New_VC_Prog
     (Ada_Node   : Node_Id;
      Expr       : W_Prog_Id;
      Reason     : VC_Kind;
      Check_Info : Check_Info_Type := New_Check_Info)
      return W_Prog_Id
   is (+New_VC_Expr (Ada_Node, +Expr, Reason, EW_Prog, Check_Info));

   function New_VC_Labels
     (N          : Node_Id;
      Reason     : VC_Kind;
      Check_Info : Check_Info_Type)
      return Symbol_Set;
   --  Generate VC and location labels for the given Ada node, with the given
   --  VC reason

   function New_Range_Expr
     (Domain    : EW_Domain;
      Low, High : W_Expr_Id;
      Expr      : W_Expr_Id;
      Pretty    : Boolean := False)
      return W_Expr_Id;
   --  Build an expression (Low <= Expr and then Expr <= High), all
   --  comparisons being in Base_Type (int or real). If Pretty is set to true,
   --  the two parts of a conjunction get a GP_Pretty_Ada attribute, which can
   --  be used for identifying the unproved part of a range or overflow check.

   function New_Range_Expr
     (Low, High : W_Term_Id;
      Expr      : W_Term_Id)
      return W_Pred_Id;

   function New_Discrete_Add
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty)
      return W_Expr_Id;
   --  @param Left Right the operand of the operation.
   --  @return an addition in either the representation type of Typ or
   --          the representation type of left if Typ is left empty; This
   --          type should either be ew_int_type or a bitvector; Will
   --          do the appropriate conversion for left and right.
   --  beware that there is no modulo operation inserted when dealing
   --  with modulars.

   function New_Discrete_Substract
     (Domain : EW_Domain;
      Left   : W_Expr_Id;
      Right  : W_Expr_Id;
      Typ    : W_Type_Id := Why_Empty)
      return W_Expr_Id;
   --  @param Typ the type of the operation
   --  @param Left Right the operand of the operation.
   --  @return a substraction in either the representation type of Typ or
   --          the representation type of left if Typ is left empty; This
   --          type should either be ew_int_type or a bitvector; Will
   --          do the appropriate conversion for left and right.
   --  beware that there is no modulo operation inserted when dealing
   --  with modulars.

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id)
      return W_Expr_Id;
   --  @param Value the value of the constant
   --  @param Typ the type of the constant
   --  @return a modular constant if Typ satisfies Why_Type_Is_BitVector
   --          or an integer constant in all other cases.

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id)
      return W_Term_Id
   is (+W_Expr_Id'(New_Discrete_Constant (Ada_Node, Value, Typ)));

   function New_Discrete_Constant
     (Ada_Node : Node_Id := Empty;
      Value    : Uint;
      Typ      : W_Type_Id)
      return W_Prog_Id
   is (+W_Expr_Id'(New_Discrete_Constant (Ada_Node, Value, Typ)));

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Expr   : W_Term_Id;
      Params : Transformation_Params := Body_Params)
      return W_Expr_Id
   with Pre => Is_Type (Ty);
   --  Function to generate a call expressing that Expr is of the dynamic type
   --  Ty.

   function Do_Range_Check
     (Ada_Node   : Node_Id;
      Ty         : Entity_Id;
      W_Expr     : W_Expr_Id;
      Check_Kind : Scalar_Check_Kind) return W_Prog_Id
   with Pre => Is_Type (Ty);
   --  Returns the Why program that does range checking on W_Expr, for type Ty

   function Insert_Conversion_To_Rep_No_Bool
     (Domain : EW_Domain;
      Expr   : W_Expr_Id)
      return W_Expr_Id;
   --  Convert argument to representation type or ew_int_id if expr is of
   --  type Bool.

   function Insert_Conversion_To_Rep_No_Bool
     (Expr : W_Term_Id)
      return W_Term_Id
   is (+Insert_Conversion_To_Rep_No_Bool (EW_Term, +Expr));

   function Do_Index_Check
     (Ada_Node : Node_Id;
      Arr_Expr : W_Term_Id;
      W_Expr   : W_Expr_Id;
      Dim      : Positive)
      return W_Prog_Id;
   --  Returns the Why program that does index checking on an index W_Expr in
   --  an array Arr_Expr.

   function Insert_Array_Conversion
     (Domain         : EW_Domain;
      Ada_Node       : Node_Id := Empty;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Need_Check     : Boolean := False;
      Force_No_Slide : Boolean := False;
      Is_Qualif      : Boolean := False;
      No_Init        : Boolean := False)
      return W_Expr_Id;
   --  Generate a conversion between two Ada array types. If Range check
   --  is set, add a length or range check to the expression. Which
   --  kind of check, and against which type, is determined by calling
   --  [Gnat2why.Nodes.Get_Range_Check_Info] on the Range_Check node.
   --  @param Ada_Node node which causes the check to be inserted.
   --  @param Domain domain of the conversion
   --  @param Expr expression to be converted
   --  @param To type to convert to
   --  @param Need_Check True if checks should be inserted
   --  @param Force_No_Slide True if we want to force no sliding to be
   --     introduced even for types with non-static bounds. Should be used
   --     with care
   --  @param In_Qualif True if the conversion is in fact a qualification. In
   --     qualifications, arrays are never slided, and index checks are
   --     introduced to ensure that the bounds match.
   --  @param No_Init True if we are converting a potentially uninitialized
   --     value (ie if want to skip initialization checks and predicate checks
   --     during the conversion).
   --  @result converted expression of Expr to type To

   function Insert_Checked_Conversion
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Lvalue   : Boolean := False;
      No_Init  : Boolean := False)
      return W_Expr_Id;
   --  Returns the expression of type To that converts Expr possibly inserting
   --  checks during the conversion.
   --  @param Ada_Node node which causes the check to be inserted. This node
   --     is used to retrieve the type and kind of check.
   --  @param Domain check is actually only inserted when domain is EW_Prog
   --  @param Expr expression to be converted
   --  @param To type to convert to
   --  @param Lvalue True iff this is applied to the left-hand side of an
   --     assignment or to in out or out parameter calls when performing copy
   --     back assignments. This has an effect on retrieving the type for the
   --     check.
   --  @param No_Init True if we are converting a potentially uninitialized
   --     value (ie if want to skip initialization checks and predicate checks
   --     during the conversion).
   --  @result converted expression of Expr to type To, with possible check

   function Insert_Simple_Conversion
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Expr           : W_Expr_Id;
      To             : W_Type_Id;
      Force_No_Slide : Boolean := False)
      return W_Expr_Id;
   --  Returns the expression Expr converted to type To. No
   --  check is inserted in the conversion.
   --  @param Ada_Node node which causes the check to be inserted.
   --  @param Domain domain of the conversion
   --  @param Expr expression to be converted
   --  @param To type to convert to
   --  @param Force_No_Slide True if we want to force no sliding to be
   --     introduced even for types with non-static bounds. Should be used
   --     only for components of records which may have discriminant
   --     constraints.
   --  @result converted expression of Expr to type To, no check

   function Insert_Simple_Conversion
     (Ada_Node       : Node_Id := Empty;
      Expr           : W_Prog_Id;
      To             : W_Type_Id;
      Force_No_Slide : Boolean := False) return W_Prog_Id
   is (+W_Expr_Id'(Insert_Simple_Conversion
       (Ada_Node, EW_Term, +Expr, To, Force_No_Slide)));

   function Insert_Simple_Conversion
     (Ada_Node       : Node_Id := Empty;
      Expr           : W_Term_Id;
      To             : W_Type_Id;
      Force_No_Slide : Boolean := False) return W_Term_Id
   is (+W_Expr_Id'(Insert_Simple_Conversion
       (Ada_Node, EW_Term, +Expr, To, Force_No_Slide)));

   function Insert_Scalar_Conversion
     (Domain   : EW_Domain;
      Ada_Node : Node_Id := Empty;
      Expr     : W_Expr_Id;
      To       : W_Type_Id;
      Do_Check : Boolean := False;
      Lvalue   : Boolean := False;
      No_Init  : Boolean := False) return W_Expr_Id;
   --  We insert a conversion on Expr so that its type corresponds to "To".
   --  When Range_Check is set, a range check is inserted into the conversion,
   --  and the node Ada_Node is used to determine the kind of the check.
   --  @param Domain domain for the returned expression
   --  @param Ada_Node node associated to the conversion
   --  @param Expr expression to be converted
   --  @param To type to convert to
   --  @param Do_Check True iff a check should be inserted
   --  @param Lvalue True iff this is applied to the left-hand side of an
   --     assignment. This has an effect on retrieving the type for the check.
   --  @param No_Init True if we are converting a potentially uninitialized
   --     value (ie if want to skip initialization checks and predicate checks
   --     during the conversion).
   --  @result converted expression of Expr to type To

   function Insert_Scalar_Conversion
     (Domain     : EW_Domain;
      Ada_Node   : Node_Id := Empty;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Range_Type : Entity_Id;
      Check_Kind : Scalar_Check_Kind;
      Lvalue     : Boolean := False;
      No_Init    : Boolean := False;
      Skip_Pred  : Boolean := False) return W_Expr_Id
   with Pre => (if Present (Range_Type) then Is_Type (Range_Type));
   --  Same as the above except that we take directly the kind of check as
   --  input.
   --  @param Skip_Pred True if we should not check the predicate if any

   function Insert_Record_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False) return W_Expr_Id;
   --  When Need_Check is set, a discriminant check is inserted into the
   --  conversion, and the node is used to determine the subtype for the check.
   --  No_Init is set if we are converting a potentially uninitialized
   --  value (ie if want to skip predicate checks during the conversion).

   function Insert_Pointer_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False) return W_Expr_Id;
   --  If Need_Check is True, insert range, null exclusion and predicate
   --  checks.
   --  No_Init is set if we are converting a potentially uninitialized
   --  value (ie if want to skip predicate checks during the conversion).

   function Insert_Subp_Pointer_Conversion
     (Ada_Node   : Node_Id;
      Domain     : EW_Domain;
      Expr       : W_Expr_Id;
      To         : W_Type_Id;
      Need_Check : Boolean := False;
      No_Init    : Boolean := False) return W_Expr_Id;
   --  If Need_Check is True, insert LSP, null exclusion and predicate
   --  checks.
   --  No_Init is set if we are converting a potentially uninitialized
   --  value (ie if want to skip predicate checks during the conversion).

   function Insert_Cnt_Loc_Label
     (Ada_Node     : Node_Id;
      E            : W_Expr_Id;
      Is_Loop_Head : Boolean := False) return W_Expr_Id;
   --  Return E with a new label for the counterexample location of Ada_Node

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Identifier_Id;
      Def      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id;
   --  same as New_Binding, but adds type information coming from Context

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Def      : W_Prog_Id;
      Context  : W_Prog_Id)
      return W_Prog_Id
   is (+W_Expr_Id'
         (New_Typed_Binding (Ada_Node, EW_Prog, Name, +Def, +Context)));

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Def      : W_Term_Id;
      Context  : W_Pred_Id)
      return W_Pred_Id
   is (+W_Expr_Id'
         (New_Typed_Binding (Ada_Node, EW_Pred, Name, +Def, +Context)));

   function New_Typed_Binding
     (Ada_Node : Node_Id := Empty;
      Name     : W_Identifier_Id;
      Def      : W_Term_Id;
      Context  : W_Term_Id)
      return W_Term_Id
   is (+W_Expr_Id'
         (New_Typed_Binding (Ada_Node, EW_Term, Name, +Def, +Context)));

   subtype Supported_Attribute_Id is Attribute_Id with
     Static_Predicate => Supported_Attribute_Id in Attribute_Alignment
                                                 | Attribute_Constrained
                                                 | Attribute_First
                                                 | Attribute_Last
                                                 | Attribute_Length
                                                 | Attribute_Modulus
                                                 | Attribute_Image
                                                 | Attribute_Value
                                                 | Attribute_Value_Size
                                                 | Attribute_Size
                                                 | Attribute_Component_Size
                                                 | Attribute_Tag;

   function New_Attribute_Expr
     (Ty     : Entity_Id;
      Domain : EW_Domain;
      Attr   : Supported_Attribute_Id;
      Params : Transformation_Params := Body_Params)
      return W_Expr_Id
   with Pre => Is_Type (Ty);
   --  Compute an expression for a type attribute Ty'Attr.
   --  @param Ty The entity for the Ada type.
   --  @param Domain The domain of the returned expression.
   --  @param Attr The querried type attribute.
   --  @param Params The parameters used for the transformation of bound
   --  expressions.
   --  @return The translated type attribute into Why3.

   function New_Binary_Op_Expr
     (Op          : N_Binary_Op;
      Left        : W_Expr_Id;
      Right       : W_Expr_Id;
      Left_Type   : Type_Kind_Id;
      Right_Type  : Type_Kind_Id;
      Return_Type : Type_Kind_Id;
      Domain      : EW_Domain;
      Ada_Node    : Node_Id := Empty)
      return W_Expr_Id
   with Pre => Op in N_Op_Add .. N_Op_Rem;
   --  @param Op arithmetic binary operator
   --  @param Left why expression for the left hand side
   --  @param Right why expression for the right hand side
   --  @param Left_Type Ada Type of the left hand side
   --  @param Right_Type Ada Type of the right hand side
   --  @param Return_Type Ada Type of the result of the operation
   --  @param Domain domain of the operation
   --  @param Ada_Node node associated to the operation
   --  @return a Why3 expression for Left Op Right

   function Transform_Non_Binary_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Type_Kind_Id;
      Domain     : EW_Domain;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint)
      return W_Expr_Id
   with
     --  GNAT does not support non-binary modulus greater than 2**32, we can
     --  use that limit to simplify treatment here.
     Pre => Modulus < UI_Expon (2, 32);
   --  For non binary modular types, it is incorrect to apply the arithmetic
   --  operations - + * on the base type and then apply the modulus on the
   --  result. The special treatment needed in this case is implemented here.
   --
   --  @param Ada_Type type of the Ada node, used to retrieve type Size in bits
   --  @param Op the operation, should be either Minus, Add, Sub or Mul
   --  @param Left_Opnd the left operand of type [Rep_Type], should be empty if
   --     Op is N_Op_Minus.
   --  @param Right_Opnd the right operand of type [Rep_Type]
   --  @param Rep_Type the representation type in which the operation is done.
   --     Both operand should already be converted to this type.
   --  @param Modulus the modulus of the type in which the operation is done.
   --     It should be a non power of two smaller than 2 ** 32.
   --  @return the Why3 expression corresponding to the operation with
   --     modulus applied. One should not call Apply_Modulus after
   --     calling this function.

   function Check_No_Wrap_Around_Modular_Operation
     (Ada_Node   : Node_Id;
      Ada_Type   : Type_Kind_Id;
      Op         : N_Op;
      Left_Opnd  : W_Expr_Id := Why_Empty;
      Right_Opnd : W_Expr_Id;
      Rep_Type   : W_Type_Id;
      Modulus    : Uint)
      return W_Prog_Id
   with Pre => Present (Ada_Node)
     and then Op in N_Op_Minus
                  | N_Op_Add
                  | N_Op_Subtract
                  | N_Op_Multiply
                  | N_Op_Expon;
   --  For modular type Ada_Type with annotation No_Wrap_Around, a check must
   --  be emitted on unary operation - and binary operations - + * **
   --
   --  @param Ada_Node the node to which the check should be attached
   --  @param Ada_Type type of the Ada node, used to retrieve type Size in bits
   --  @param Op the operation, should be either Minus, Add, Sub, Mul or Expon
   --  @param Left_Opnd the left operand of type [Rep_Type], should be empty if
   --     Op is N_Op_Minus.
   --  @param Right_Opnd the right operand of type [Rep_Type] for Add, Sub, Mul
   --     or type int for Expon
   --  @param Rep_Type the representation type in which the operation is done.
   --     Both operand should already be converted to this type for Add, Sub,
   --     Mul, only the first operand for Expon while the second is of type int
   --  @param Modulus the modulus of the type in which the operation is done
   --  @return the Why3 check expression

   function Apply_Modulus
     (Op     : N_Op;
      E      : Type_Kind_Id;
      T      : W_Expr_Id;
      Domain : EW_Domain)
      return W_Expr_Id;
   --  If E is a modular type, apply a modulus on T, else return T unchanged.
   --  Beware that for additions, substractions and multiplications on a
   --  modular type with a modulus that is not a power of two, it is not
   --  correct to use this function. Instead, one should directly use
   --  "Transform_Non_Binary_Modular_Operation" to deal with the whole
   --  transformation.
   --  Optimization: if E is a modular type, and Op is a division, do not add
   --  the modulus operation.

   function Transform_Compare_Op
     (Op     : N_Op_Compare;
      Ty     : W_Type_Id;
      Domain : EW_Domain)
      return W_Identifier_Id;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Get_Type (E : W_Expr_Id) return W_Type_Id;
   --  extract the type of a given expression

   function New_Havoc_Call (Id : W_Identifier_Id) return W_Prog_Id;
   --  @param Id Identifier of a variable
   --  @result Program havocing the value of Id

   -------------------------------------
   -- Introducing temporary variables --
   -------------------------------------

   --  The following two functions are intended to be used as follows:
   --  Tmp : W_Expr_Id := New_Temp_For_Expr (E);
   --  .... build a complex expression R using Tmp ...
   --  Result : W_Expr_Id := Binding_For_Temp (Tmp, R);

   --  the result is that a temporary variable is introduced (when necessary)
   --  for E, which is used in the complex expression. The user of these two
   --  functions just uses "Tmp" everywhere and can forget about "E". The call
   --  to Binding_For_Temp puts the let-binding on top of the resulting term,
   --  or simply returns "Context" when no temp was in fact necessary.

   function New_Temp_For_Expr
     (E         : W_Expr_Id;
      Need_Temp : Boolean := True) return W_Expr_Id;
   --  Return a temp variable for the given expression, and store the provided
   --  expression for later use. If Need_Temp is False, do not actually
   --  introduce a temp variable.

   function New_Temp_For_Expr (E : W_Prog_Id) return W_Prog_Id
   is (+W_Expr_Id'(New_Temp_For_Expr (+E, Need_Temp => True)));

   function New_Temp_For_Expr (E : W_Term_Id) return W_Term_Id
   is (+W_Expr_Id'(New_Temp_For_Expr (+E, Need_Temp => True)));

   function New_Temp_For_Expr (E : W_Expr_Id) return W_Term_Id
   is (+W_Expr_Id'(New_Temp_For_Expr (E, Need_Temp => True)));
   --  Take an arbitrary expression in parameter (possibly a program one),
   --  while still returning a term, which is useful in some cases.

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Tmp      : W_Expr_Id;
      Context  : W_Expr_Id)
      return W_Expr_Id;
   --  Introduce a let binding for Tmp on top of "Context". The value of Tmp is
   --  the one provided to the corresponding call to New_Temp_For_Expr.

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Tmp      : W_Term_Id;
      Context  : W_Pred_Id)
      return W_Pred_Id
   is (+W_Expr_Id'(Binding_For_Temp (Ada_Node, EW_Pred, +Tmp, +Context)));

   function Binding_For_Temp
     (Ada_Node : Node_Id := Empty;
      Tmp      : W_Term_Id;
      Context  : W_Prog_Id)
      return W_Prog_Id
   is (+W_Expr_Id'(Binding_For_Temp (Ada_Node, EW_Prog, +Tmp, +Context)));

end Why.Gen.Expr;
