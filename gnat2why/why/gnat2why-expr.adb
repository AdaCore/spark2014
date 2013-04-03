------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        G N A T 2 W H Y - E X P R                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;

with GNAT.Source_Info;

with Ada.Containers;         use Ada.Containers;

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Eval_Fat;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Opt;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Stand;                  use Stand;
with Uintp;                  use Uintp;
with Urealp;                 use Urealp;

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Why;                    use Why;
with Why.Unchecked_Ids;      use Why.Unchecked_Ids;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Gen.Arrays;         use Why.Gen.Arrays;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Gen.Records;        use Why.Gen.Records;
with Why.Gen.Terms;          use Why.Gen.Terms;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Conversions;        use Why.Conversions;

with Gnat2Why.Decls;         use Gnat2Why.Decls;
with Gnat2Why.Expr.Loops;    use Gnat2Why.Expr.Loops;
with Gnat2Why.Types;         use Gnat2Why.Types;

package body Gnat2Why.Expr is

   --  This package handles the translation of expressions and statements to
   --  Why.

   --  -----------------------------
   --  Handling of 'Image and 'Value
   --  -----------------------------
   --
   --  For each scalar type, we introduce functions corresponding to 'Image and
   --  'Value. Logically, the return type of 'Image and the argument type of
   --  'Value should be Standard__String, but this would be circular, as String
   --  depends on a scalar type itself. Therefore, we introduce an abstract
   --  type __image, which is used as return type/argument type of the Why3
   --  functions for 'Image and 'Value. In addition, in the Why3 module for
   --  Standard__String, we generate two conversion functions between __image
   --  and String. The actual translation of the attributes now needs to use
   --  these conversion functions to get an actual String from a scalar, or
   --  to be able to convert a string to a scalar. So X'Image gets converted to
   --
   --  Standard__String.to_string (attr__ATTRIBUTE_IMAGE (to_int (x)))
   --
   --  Finally, to express that 'Value may fail, there is also a program
   --  function that corresponds to 'Value, that has an unprovable
   --  precondition, and "true" as postcondition.

   --  Code pointers:
   --    * Why3 declarations for type __image and the attributes Image
   --      and Value: see file ada__model.mlw.
   --    * Special case for the Standard__String module: see
   --      why-gen-arrays.adb:Declare_Unconstrained_Array
   --    * handling of the attributes: Transform_Attr in this file.

   ---------------------
   -- Local Variables --
   ---------------------

   function Str_Hash (X : String_Id) return Hash_Type is (Hash_Type (X));

   package Strlit_To_Why is new Hashed_Maps (Key_Type        => String_Id,
                                             Element_Type    => Why_Node_Id,
                                             Hash            => Str_Hash,
                                             Equivalent_Keys => "=",
                                             "="             => "=");

   package Strlit_To_Type is new
     Hashed_Maps (Key_Type        => String_Id,
                  Element_Type    => W_Base_Type_Id,
                  Hash            => Str_Hash,
                  Equivalent_Keys => "=",
                  "="             => "=");

   Ada_To_Why_Func : Ada_To_Why.Map;
   --  Mappings from Ada nodes to Why logic functions for their translation
   Strlit_To_Why_Term : Strlit_To_Why.Map;
   Strlit_To_Why_Type : Strlit_To_Type.Map;
   --  Idem for string literals, where the Ref_Allowed information is not
   --  needed.

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Apply_Modulus
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain)
       return W_Expr_Id;
   --  Apply a modulus on T, where the modulus is defined by the Entity N
   --  which must be a modular type. If E is not a modular type, return T
   --  unchanged.

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id) return W_Expr_Id
     with Pre => Is_Scalar_Type (In_Type);
   --  Inserts an overflow check on top of the Why expression T, using the
   --  bounds of the base type of In_Type. Use Ada_Node for the VC location.

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Base_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id;
   --  Build Case expression of Ada Node.

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Transformation_Params) return W_Expr_Array;
   --  Compute arguments for a function call or procedure call. The node in
   --  argument must have a "Name" field and a "Parameter_Associations" field.
   --  Nb_Of_Refs is the number of ref arguments that could not be
   --  translated "as is" (because of a type mismatch) and for which
   --  Insert_Ref_Context must be called.

   function Why_Subp_Has_Precondition (E : Entity_Id) return Boolean;
   --  Return true whenever the Why declaration that corresponds to the given
   --  subprogram has a precondition.

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean;
   --  Return whether Choice is a range ("others" counts as a range)

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id)
     return Boolean;
   --  True if the parameter passing needs a temporary ref to be performed.

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive) return W_Prog_Id;
   --  Considering a call to an Ada subprogram; Ada_Call being its node
   --  in the Ada syntax tree, and Why_Call its corresponding call in the
   --  Why syntax tree:
   --
   --  For all "out"/"in out" parameters that need a conversion, generate
   --  the whole context around the call, using a temporary variable
   --  which is named after the corresponding formal. e.g. something of the
   --  form:
   --
   --   let formal := ref (to_formal_type_ (from_actual_type (!actual))) in
   --    (<why_call> ;
   --     actual := to_actual_type_ (from_formal_type (!formal))
   --
   --  Nb_Of_Refs should be set to the number of such parameters in Ada_Call.

   function Is_Pretty_Node (N : Node_Id) return Boolean;
   --  Decide whether this is a node where we should put a pretty printing
   --  label, or if we should descend further

   generic
      with procedure Handle_Argument (Formal, Actual : Node_Id);
   procedure Iterate_Call_Arguments (Call : Node_Id);
   --  Call "Handle_Argument" for each pair Formal/Actual of a function or
   --  procedure call. The node in argument must have a "Name" field and a
   --  "Parameter_Associations" field.

   function One_Level_Access
     (N           : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params;
      Current_Type : out W_Base_Type_Id) return W_Expr_Id;
   --  Compute an access expression for record and array accesses without
   --  considering subexpressions. [N] represents the Ada node of the access,
   --  and [Expr] the Why expression of the prefix.

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Prefix_Type : Entity_Id;
      Val_Type    : Entity_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  same as One_Level_Access, but for updates

   function Expected_Type_Of_Prefix (N : Node_Id) return Entity_Id;
   --  ??? The comment below is incorrect, as Expected_Type_Of_Prefix is called
   --  for every assignment, not only assignment to record components and array
   --  cells. To be checked.
   --
   --  The node in argument is some array or record access. This function
   --  computes the type of the entity that corresponds to the access.
   --  This may be different from the Etype of the node in case of
   --  unconstrained array types, or discriminant records.

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id;

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id;
   --  For an expression Expr of a type EW_Int and a discrete Choice, build
   --  the expression that Expr belongs to the range expressed by Choice.

   function Transform_Identifier (Params       : Transformation_Params;
                                  Expr         : Node_Id;
                                  Ent          : Entity_Id;
                                  Domain       : EW_Domain;
                                  Current_Type : out W_Base_Type_Id)
                                  return W_Expr_Id;
   --  Transform an Ada identifier to a Why item (take care of enumeration
   --  literals, boolean values etc)

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id;

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id;
   --  Transform a declaration. Return a program that takes into account the
   --  dynamic semantics of the declaration (checks and assumptions).

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl   : Node_Id;
      Assert_And_Cut : out W_Pred_Id) return W_Prog_Id;
   --  Transform the Ada statement into a Why program expression.
   --  If Assert_And_Cut is not Why_Empty, the statement was a "pragma
   --  Assert_And_Cut". In this case, Assert_And_Cut contains the
   --  Why3 predicate equivalent of the assertion expression, and
   --  Transform_Statement contains the check program expression
   --  that corresponds to the assertion expression.

   function Transform_Aggregate
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id;
   --  Transform an aggregate Expr. It may be called multiple times on the
   --  same Ada node, corresponding to different phases of the translation. The
   --  first time it is called on an Ada node, a logic function is generated
   --  and stored in Ada_To_Why_Func, so that the function and axiom are
   --  generated only once per source aggregate. This function F is used
   --  for generating each translation of this node. It takes in parameters
   --  all components passed to the aggregate. This is simply the list of
   --  components for a one-dimensional aggregate, and it takes into account
   --  sub-components for multi-dimensional aggregates.
   --
   --     function F (<params>) : <type of aggregate>
   --
   --     axiom A:
   --        forall R:<type of aggregate>. forall <params>.
   --           R = F(<params>) -> <proposition for the aggregate R>
   --
   --  On the aggregate (1 => X, others => Y), components are {X, Y}.
   --  On the aggregate (1 => (1 => X, others => Y), 2 => Z), components are
   --  {X, Y, Z}.

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id;
   --  Transform a slice Expr. It may be
   --  called multiple times on the same Ada node, corresponding to different
   --  phases of the translation. The first time it is called on an Ada node,
   --  a logic function is generated and stored in Ada_To_Why_Func, so that the
   --  function and axiom are generated only once per source slice. This
   --  function F is used for generating each translation of this node. It
   --  takes in parameters the prefix and bounds of the slice.
   --
   --     function F (prefix:<type>, low:int, high:int) : <type>
   --
   --     axiom A:
   --        forall id:<type>. forall low:int. forall high:int.
   --           R = F(id,low,high) -> <proposition for the slice R>

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id;
   --  Translate a single Ada statement into a Why expression

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Val_Type : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id;
   --  Translate an assignment of the form "Lvalue := Expr",
   --  using Ada_Node for its source location. [Val_Type] is the type of
   --  [Expr], and the type of the innermost component of the Lvalue.

   ------------------------------------------
   -- Handling of Expressions with Actions --
   ------------------------------------------

   --  The detection phase currently allows 3 kinds of nodes in actions:
   --    N_Object_Declaration for constants
   --    N_Subtype_Declaration
   --    N_Full_Type_Declaration

   --  Declarations of constant objects are transformed into let-binding in
   --  Why, which is possible in any context (program, term, proposition).

   --  Declarations of types are simply ignored. Indeed, we don't know how to
   --  translate the assignment to type bounds like done in
   --  Transform_Declaration in a proposition context. Note that this choice
   --  can possibly lead to dynamic bounds not known at VC level, if such types
   --  are introduced in actions.

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id;
   --  Translate a list of Actions, that should consist only in declarations of
   --  constants used in Expr.

   procedure Transform_Actions_Preparation
     (Actions : List_Id;
      Params  : in out Transformation_Params);
   --  Update the map in Params for taking into account the names for
   --  declarations of constants in Actions.

   function Transform_Attr
     (Expr               : Node_Id;
      Domain             : EW_Domain;
      Current_Type       : out W_Base_Type_Id;
      Params             : Transformation_Params) return W_Expr_Id;
   --  Range_Check_Needed is set to True for some attributes (like 'Pos,
   --  'Length, 'Modulus) which return a universal integer, so that we check
   --  the result fits in the actual type used for the node.

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id);
   --  Create an uninterpreted logic function with no parameters that returns a
   --  string value corresponding to the string literal.

   function Transform_Record_Component_Associations
     (Domain      : EW_Domain;
      Typ         : Entity_Id;
      Assocs      : List_Id;
      Params      : Transformation_Params) return W_Field_Association_Array;

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op;
   --  Convert an Ada binary operator to a Why term symbol

   function Transform_Enum_Literal
     (Expr         : Node_Id;
      Enum         : Entity_Id;
      Current_Type : out W_Base_Type_Id;
      Domain       : EW_Domain)
      return W_Expr_Id;
   --  Translate an Ada enumeration literal to Why. There are a number of
   --  special cases, so its own function is appropriate.

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation;
   --  Convert an Ada comparison operator to a Why relation symbol

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id)
      return W_Expr_Id;
   --  Convert a membership expression (N_In) into a boolean Why expression

   -------------------
   -- Apply_Modulus --
   -------------------

   function Apply_Modulus
      (E                     : Entity_Id;
       T                     : W_Expr_Id;
       Domain                : EW_Domain)
      return W_Expr_Id
   is
   begin
      if Is_Modular_Integer_Type (E) then
         return
            New_Call (Name => To_Ident (WNE_Integer_Mod),
                      Domain => Domain,
                      Args =>
                       (1 => T,
                        2 => New_Integer_Constant
                                (Value => Modulus (E))));
      else
         return T;
      end if;
   end Apply_Modulus;

   ----------------------------
   -- Assignment_Of_Obj_Decl --
   ----------------------------

   function Assignment_Of_Obj_Decl (N : Node_Id) return W_Prog_Id
   is
      Lvalue   : constant Entity_Id := Defining_Identifier (N);
      Rexpr    : constant Node_Id := Expression (N);
   begin

      --  In our Why translation, all objects are declared at top-level.
      --  Object declarations in Ada inside Subprograms are therefore
      --  translated to assignments to initialize these objects.
      --  We can only generate an assignment when the Lvalue is mutable; if it
      --  is not, there are two cases. If the expression is static, we already
      --  have generated an axiom upon declaration of the object, and we are
      --  done. If it is not, we replace the assignment by an assumption of
      --  the following form:

      --  let var_name__assume = <rexpr> in
      --    assume (var_name = var_name_assume);

      if Present (Rexpr) then
         declare
            Why_Expr : constant W_Prog_Id :=
                         +Transform_Expr (Rexpr,
                                          Type_Of_Node (Lvalue),
                                          EW_Prog,
                                          Params => Body_Params);
            L_Name   : constant String := Full_Name (Lvalue);
            L_Id     : constant W_Identifier_Id := To_Why_Id (Lvalue);
         begin
            if Is_Mutable_In_Why (Lvalue) then
               return New_Assignment
                 (Ada_Node => N,
                  Name     => L_Id,
                  Value    => Why_Expr);

            elsif Is_Static_Expression (Rexpr) then

               --  We generate an ignore statement, to obtain all the checks
               --  ??? Is this necessary? after all, we would get a compiler
               --  warning anyway

               return New_Ignore (Prog => Why_Expr);

            else
               declare
                  Tmp_Var : constant W_Identifier_Id :=
                              Assume_Name.Id (L_Name);
                  Eq      : constant W_Pred_Id :=
                              New_Relation
                                (Op      => EW_Eq,
                                 Op_Type => Get_EW_Type (Lvalue),
                                 Left    => +Tmp_Var,
                                 Right   => +L_Id);
               begin
                  return
                    New_Binding
                      (Ada_Node => N,
                       Name     => Tmp_Var,
                       Def      => +Why_Expr,
                       Context  =>
                         +New_Assume_Statement
                           (Ada_Node => N,
                            Post     => Eq));
               end;
            end if;
         end;
      else
         return New_Void (N);
      end if;
   end Assignment_Of_Obj_Decl;

   ------------------------------
   -- Assume_Of_Scalar_Subtype --
   ------------------------------

   function Assume_Of_Scalar_Subtype
     (Params : Transformation_Params;
      N      : Entity_Id;
      Base   : Entity_Id) return W_Prog_Id
   is
      Rng              : constant Node_Id := Get_Range (N);
      Why_Base         : constant W_Base_Type_Id := Base_Why_Type (N);
      Why_Base_EW      : constant EW_Type := Get_EW_Type (N);
      Low_Expr         : constant W_Term_Id :=
         +Transform_Expr (Low_Bound (Rng), Why_Base, EW_Term, Params);
      High_Expr        : constant W_Term_Id :=
         +Transform_Expr (High_Bound (Rng), Why_Base, EW_Term, Params);
      First_Term       : constant W_Term_Id :=
        +New_Attribute_Expr (N, Attribute_First);
      Last_Term        : constant W_Term_Id :=
        +New_Attribute_Expr (N, Attribute_Last);
      Rel_First        : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => EW_Bool,
            Left     => +Low_Expr,
            Right    => +First_Term,
            Op       => EW_Eq);
      Rel_Last         : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => EW_Bool,
            Left     => +High_Expr,
            Right    => +Last_Term,
            Op       => EW_Eq);
      First_In_Range   : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +Low_Expr,
            Right    => +New_Attribute_Expr (Base, Attribute_First),
            Op       => EW_Ge);
      Last_In_Range    : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +High_Expr,
            Right    => +New_Attribute_Expr (Base, Attribute_Last),
            Op       => EW_Le);
      First_Le_Last    : constant W_Pred_Id :=
         New_Relation
           (Op_Type  => Why_Base_EW,
            Left     => +Low_Expr,
            Right    => +High_Expr,
            Op       => EW_Le);
      Precond          : constant W_Pred_Id :=
         +New_Connection
           (Op     => EW_Imply,
            Left   => +First_Le_Last,
            Right  =>
              +New_And_Expr
                 (Domain => EW_Pred,
                  Left   => +First_In_Range,
                  Right => +Last_In_Range));
      Assuming        : constant W_Prog_Id :=
        New_Assume_Statement
          (Ada_Node => N,
           Pre      => Precond,
           Post     =>
           +New_And_Expr
             (Domain => EW_Pred,
              Left   => +Rel_First,
              Right  => +Rel_Last));
   begin
      return
        +New_VC_Expr
        (Ada_Node => N,
         Domain   => EW_Prog,
         Reason   => VC_Range_Check,
         Expr     => +Assuming);
   end Assume_Of_Scalar_Subtype;

   ----------------------------------
   -- Assume_Of_Subtype_Indication --
   ----------------------------------

   function Assume_Of_Subtype_Indication
     (Params : Transformation_Params;
      N      : Node_Id) return W_Prog_Id is
   begin
      if Nkind (N) = N_Subtype_Indication then
         return
           Assume_Of_Scalar_Subtype
             (Params, Etype (N), Etype (Subtype_Mark (N)));
      else
         return New_Void;
      end if;
   end Assume_Of_Subtype_Indication;

   -------------------------------
   -- Bind_From_Mapping_In_Expr --
   -------------------------------

   function Bind_From_Mapping_In_Expr
     (Params                 : Transformation_Params;
      Map                    : Ada_To_Why_Ident.Map;
      Expr                   : W_Prog_Id;
      Do_Runtime_Error_Check : Boolean := True) return W_Prog_Id
   is
      Result : W_Prog_Id := Expr;
   begin
      for C in Map.Iterate loop
         declare
            N    : constant Node_Id := Ada_To_Why_Ident.Key (C);
            Name : constant W_Identifier_Id := Ada_To_Why_Ident.Element (C);

            --  Generate a program expression to check absence of run-time
            --  errors.

            RE_Prog : constant W_Prog_Id :=
              (if Do_Runtime_Error_Check then
                 New_Ignore (Prog => +Transform_Expr (N, EW_Prog, Params))
               else
                 New_Void);

            --  Generate a term definition for the value of the object at
            --  subprogram entry, and link with rest of code. This
            --  definition does not involve lazy boolean operators, so it
            --  does not lead to more paths being generated in the naive WP,
            --  contrary to what we would get if directly defining the value
            --  of the object as a program. This is particularly useful for
            --  guards of Contract_Cases.

            Let_Prog : constant W_Prog_Id :=
                            New_Binding
                              (Name   => Name,
                               Def    =>
                               +New_Simpl_Any_Prog
                                 (T    => Why_Logic_Type_Of_Ada_Obj (N),
                                  Pred =>
                                  +W_Expr_Id'(New_Relation
                                    (Domain   => EW_Pred,
                                     Op_Type  => EW_Bool,
                                     Left     => +To_Ident (WNE_Result),
                                     Op       => EW_Eq,
                                     Right    =>
                                     +Transform_Expr (N, EW_Term, Params)))),
                               Context => +Result);
         begin
            Result := Sequence (RE_Prog, Let_Prog);
         end;
      end loop;

      return Result;
   end Bind_From_Mapping_In_Expr;

   ---------------------------
   -- Case_Expr_Of_Ada_Node --
   ---------------------------

   function Case_Expr_Of_Ada_Node
     (N             : Node_Id;
      Expected_Type : W_Base_Type_OId := Why_Empty;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      --  For a given case expression
      --
      --    case X is
      --       when Case_1 => S1
      --       ...
      --       when Case_n => Sn
      --       when others => S
      --    end case;
      --
      --  We generate a single if expression, with a list of elsif cases, to
      --  avoid the generation of deep Why3 expressions, which may lead to
      --  stack overflow when traversing recursively the expression:
      --
      --    if X = Case_1 then S1
      --    elsif ...
      --    elsif X = Case_N then Sn
      --    else S

      function Branch_Expr (N : Node_Id) return W_Expr_Id;
      --  Return the expression that corresponds to a branch; decide which
      --  function to call depending on the type of the branch.

      -----------------
      -- Branch_Expr --
      -----------------

      function Branch_Expr (N : Node_Id) return W_Expr_Id is
         Local_Params : Transformation_Params := Params;
         T : W_Expr_Id;

      begin
         case Nkind (N) is
            when N_Case_Expression_Alternative =>
               if Present (Actions (N)) then
                  Transform_Actions_Preparation (Actions (N), Local_Params);
               end if;

               if Expected_Type = Why_Empty then
                  T := Transform_Expr (Expression (N),
                                       Domain,
                                       Local_Params);
               else
                  T := Transform_Expr (Expression (N),
                                       Expected_Type,
                                       Domain,
                                       Local_Params);
               end if;

               if Present (Actions (N)) then
                  T := Transform_Actions (Actions (N),
                                          T,
                                          Domain,
                                          Local_Params);
               end if;

               return T;

            when N_Case_Statement_Alternative =>
               --  ??? Maybe we should merge the code for statements?
               return +Transform_Statements_And_Declarations (Statements (N));

            when others =>
               raise Unexpected_Node;

         end  case;
      end Branch_Expr;

      Match_Domain : constant EW_Domain :=
         (if Domain = EW_Pred then EW_Term else Domain);
      Cond_Domain  : constant EW_Domain :=
         (if Domain = EW_Term then EW_Pred else Domain);

      Cases        : constant List_Id := Alternatives (N);
      First_Case   : constant Node_Id := First (Cases);
      Last_Case    : constant Node_Id := Last (Cases);
      Cur_Case     : Node_Id;
      Matched_Expr : constant W_Expr_Id :=
                       Transform_Expr (Expression (N),
                                       EW_Int_Type,
                                       Match_Domain,
                                       Params);
      Elsif_Parts  : W_Expr_Array (1 .. Integer (List_Length (Cases)) - 2);

      --  beginning of processing for Case_Expr_Of_Ada_Node
   begin
      if List_Length (Cases) = 1 then
         return Branch_Expr (First_Case);

      else
         Cur_Case := Next (First_Case);
         for Offset in 1 .. List_Length (Cases) - 2 loop
            Elsif_Parts (Integer (Offset)) :=
              New_Elsif
                (Domain    => Domain,
                 Condition =>
                   Transform_Discrete_Choices (Case_N       => Cur_Case,
                                               Matched_Expr => Matched_Expr,
                                               Cond_Domain  => Cond_Domain,
                                               Params       => Params),
                 Then_Part => Branch_Expr (Cur_Case));
            Next (Cur_Case);
         end loop;

         return New_Conditional
           (Domain      => Domain,
            Condition   =>
              Transform_Discrete_Choices (Case_N       => First_Case,
                                          Matched_Expr => Matched_Expr,
                                          Cond_Domain  => Cond_Domain,
                                          Params       => Params),
            Then_Part   => Branch_Expr (First_Case),
            Elsif_Parts => Elsif_Parts,
            Else_Part   => Branch_Expr (Last_Case));
      end if;
   end Case_Expr_Of_Ada_Node;

   -----------------------
   -- Compute_Call_Args --
   -----------------------

   function Compute_Call_Args
     (Call        : Node_Id;
      Domain      : EW_Domain;
      Nb_Of_Refs  : out Natural;
      Params      : Transformation_Params) return W_Expr_Array
   is
      Subp   : constant Entity_Id := Entity (Name (Call));
      Assocs : constant List_Id := Parameter_Associations (Call);
      Len    : Nat;
      Read_Names : constant Name_Set.Set := Get_Reads (Subp);
   begin
      Nb_Of_Refs := 0;
      Len := List_Length (Assocs);

      if Domain = EW_Term then
         Len := Len + Int (Read_Names.Length);
      end if;

      if Len = 0 then
         return (1 => New_Void (Call));
      end if;

      declare
         Why_Args : W_Expr_Array := (1 .. Integer (Len) => <>);
         Cnt      : Positive := 1;

         procedure Compute_Arg (Formal, Actual : Node_Id);
         --  Compute a Why expression for each parameter

         -----------------
         -- Compute_Arg --
         -----------------

         procedure Compute_Arg (Formal, Actual : Node_Id)
         is
         begin
            case Ekind (Formal) is
               when E_In_Out_Parameter | E_Out_Parameter =>

                  --  Parameters that are "out" are refs;
                  --  if the actual is a simple identifier and no conversion
                  --  is needed, it can be translated "as is".

                  if not Needs_Temporary_Ref (Actual, Formal) then
                     Why_Args (Cnt) :=
                       +New_Identifier (Ada_Node => Actual,
                                        Name     => Full_Name (Actual));

                  --  If a conversion or a component indexing is needed,
                  --  it can only be done for a value. That is to say,
                  --  something of this sort should be generated:
                  --
                  --  let formal = ref to_formal (!actual) in
                  --   (subprogram_call (formal); actual := !formal)
                  --
                  --  The generation of the context is left to the caller;
                  --  this function only signals the existence of such
                  --  parameters by incrementing Nb_Of_Refs.

                  else

                     --  We should never use the Formal for the Ada_Node,
                     --  because there is no real dependency here; We only
                     --  use the Formal to get a sensible name.

                     Why_Args (Cnt) :=
                       +New_Identifier (Ada_Node => Empty,
                                        Name     => Full_Name (Formal));
                     Nb_Of_Refs := Nb_Of_Refs + 1;
                  end if;

               when others =>
                  --  No special treatment for parameters that are
                  --  not "out"
                  Why_Args (Cnt) :=
                    Transform_Expr (Actual,
                                    Type_Of_Node (Formal),
                                    Domain,
                                    Params);
            end case;
            Cnt := Cnt + 1;
         end Compute_Arg;

         procedure Iterate_Call is new
           Iterate_Call_Arguments (Compute_Arg);
      begin
         Iterate_Call (Call);

         if Domain = EW_Term then
            for Elt of Read_Names loop
               declare
                  C : constant Ada_Ent_To_Why.Cursor :=
                        Ada_Ent_To_Why.Find (Params.Name_Map, Elt.all);
                  T : W_Expr_Id;
               begin
                  --  If the effect parameter is found in the map, use the name
                  --  stored.

                  if Ada_Ent_To_Why.Has_Element (C) then
                     T := +Ada_Ent_To_Why.Element (C);
                  else
                     T := +To_Why_Id (Elt.all);
                  end if;

                  if Params.Ref_Allowed then
                     Why_Args (Cnt) := New_Deref (Right => +T);
                  else
                     Why_Args (Cnt) := T;
                  end if;
               end;
               Cnt := Cnt + 1;
            end loop;

            --  We also need to add inclusions to allow the usage of those read
            --  variables

            Add_Effect_Imports (Params.Theory, Read_Names);
         end if;

         return Why_Args;
      end;
   end Compute_Call_Args;

   ------------------------------
   -- Discrete_Choice_Is_Range --
   ------------------------------

   function Discrete_Choice_Is_Range (Choice : Node_Id) return Boolean is
      Is_Range : Boolean;
   begin
      case Nkind (Choice) is
         when N_Subtype_Indication | N_Range =>
            Is_Range := True;
         when N_Identifier | N_Expanded_Name =>
            if Ekind (Entity (Choice)) in Type_Kind then
               Is_Range := True;
            else
               Is_Range := False;
            end if;
         when N_Others_Choice =>
            Is_Range := True;
         when others =>
            Is_Range := False;
      end case;
      return Is_Range;
   end Discrete_Choice_Is_Range;

   -----------------------------
   -- Expected_Type_Of_Prefix --
   -----------------------------

   function Expected_Type_Of_Prefix (N : Node_Id) return Entity_Id
   is
   begin
      case Nkind (N) is
         when N_Identifier | N_Expanded_Name =>
            return Type_Of_Node (N);

         when N_Slice =>
            return Type_Of_Node (Unique_Entity (Etype (Prefix (N))));

         when N_Indexed_Component =>
            return Type_Of_Node
              (Component_Type (Unique_Entity (Etype (Prefix (N)))));

         when N_Selected_Component =>
            return Type_Of_Node (Selector_Name (N));

         when others =>
            Ada.Text_IO.Put_Line ("[Expected_Type] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end Expected_Type_Of_Prefix;

   ---------------------------------------------
   -- Get_Container_In_Iterator_Specification --
   ---------------------------------------------

   function Get_Container_In_Iterator_Specification
     (N : Node_Id) return Node_Id
   is
      Iter : constant Node_Id := Name (N);
   begin
      pragma Assert
        (Nkind (Iter) = N_Function_Call
         and then Is_Entity_Name (Name (Iter))
         and then Location_In_Formal_Containers (Sloc (Entity (Name (Iter)))));
      return First (Parameter_Associations (Iter));
   end Get_Container_In_Iterator_Specification;

   -------------------------------------
   -- Get_Pure_Logic_Term_If_Possible --
   -------------------------------------

   function Get_Pure_Logic_Term_If_Possible
     (File          : Why_File;
      Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id) return W_Term_Id
   is
      Params : constant Transformation_Params :=
        (Theory      => File.Cur_Theory,
         File        => File.File,
         Phase       => Generate_Logic,
         Gen_Image   => False,
         Ref_Allowed => True,
         Name_Map    => Ada_Ent_To_Why.Empty_Map);
      Result : constant W_Term_Id :=
        +Transform_Expr (Expr, Expected_Type, EW_Term, Params);
   begin
      if Has_Dereference_Or_Any (Result) then
         return Why_Empty;
      else
         return Result;
      end if;
   end Get_Pure_Logic_Term_If_Possible;

   --------------------------
   -- Get_Range_Check_Info --
   --------------------------

   procedure Get_Range_Check_Info
     (Expr       : Node_Id;
      Check_Type : out Entity_Id;
      Check_Kind : out VC_Kind)
   is
      Par : constant Node_Id := Parent (Expr);

   begin
      --  Set the appropriate entity in Check_Type giving the bounds for the
      --  check, depending on the parent node Par.

      case Nkind (Par) is

         when N_Assignment_Statement =>
            Check_Type := Etype (Name (Par));

         --  For an array access, retrieve the type for the corresponding index

         when N_Indexed_Component =>

            Indexed_Component : declare
               Obj        : constant Node_Id := Prefix (Par);
               Array_Type : Entity_Id;
               Act_Cursor : Node_Id;
               Ty_Cursor  : Node_Id;
               Found      : Boolean;

            begin
               --  When present, the Actual_Subtype of the entity should be
               --  used instead of the Etype of the prefix.

               if Is_Entity_Name (Obj)
                 and then Present (Actual_Subtype (Entity (Obj)))
               then
                  Array_Type := Actual_Subtype (Entity (Obj));
               else
                  Array_Type := Etype (Obj);
               end if;

               --  Find the index type that corresponds to the expression

               Ty_Cursor  := First_Index (Unique_Entity (Array_Type));
               Act_Cursor := First (Expressions (Par));
               Found      := False;
               while Present (Act_Cursor) loop
                  if Expr = Act_Cursor then
                     Check_Type := Etype (Ty_Cursor);
                     Found := True;
                     exit;
                  end if;

                  Next (Act_Cursor);
                  Next_Index (Ty_Cursor);
               end loop;

               --  The only possible child node of an indexed component with a
               --  range check should be one of the expressions, so Found
               --  should always be True at this point.

               if not Found then
                  raise Program_Error;
               end if;
            end Indexed_Component;

         when N_Type_Conversion =>
            Check_Type := Etype (Par);

         when N_Qualified_Expression =>
            Check_Type := Etype (Par);

         when N_Simple_Return_Statement =>
            Check_Type :=
              Etype (Return_Applies_To (Return_Statement_Entity (Par)));

         --  For a call, retrieve the type for the corresponding argument

         when N_Function_Call            |
              N_Procedure_Call_Statement |
              N_Parameter_Association    =>

            Call : declare

               Found : Boolean := False;

               procedure Check_Call_Arg (Formal, Actual : Node_Id);
               --  If Actual is the right expression, set Check_Type to the
               --  Etype of Formal.

               --------------------
               -- Check_Call_Arg --
               --------------------

               procedure Check_Call_Arg (Formal, Actual : Node_Id) is
               begin
                  if Expr = Actual then
                     Check_Type := Etype (Formal);
                     Found := True;
                  end if;
               end Check_Call_Arg;

               procedure Find_Expr_in_Call_Args is new
                 Iterate_Call_Arguments (Check_Call_Arg);

            begin
               if Nkind (Par) = N_Parameter_Association then
                  Find_Expr_in_Call_Args (Parent (Par));
               else
                  Find_Expr_in_Call_Args (Par);
               end if;

               --  The only possible child node of a call with a range check
               --  should be one of the arguments, so Found should always be
               --  True at this point.

               if not Found then
                  raise Program_Error;
               end if;
            end Call;

         when N_Attribute_Reference =>
            Attribute : declare
               Aname   : constant Name_Id := Attribute_Name (Par);
               Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
            begin
               case Attr_Id is
                  when Attribute_Pred |
                       Attribute_Succ |
                       Attribute_Val  =>
                     Check_Type := Base_Type (Entity (Prefix (Par)));

                  when others =>
                     Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] attr ="
                                           & Attribute_Id'Image (Attr_Id));
                     raise Program_Error;
               end case;
            end Attribute;

         when N_Object_Declaration =>
            Check_Type := Etype (Defining_Identifier (Par));

         when others =>
            Ada.Text_IO.Put_Line ("[Get_Range_Check_Info] kind ="
                                  & Node_Kind'Image (Nkind (Par)));
            raise Program_Error;
      end case;

      --  If the parent expression is an array access, this is an index check

      if Nkind (Par) = N_Indexed_Component then
         Check_Kind := VC_Index_Check;

         --  If the target type is a constrained array, we have a length check.

      elsif Is_Array_Type (Check_Type) and then
        Is_Constrained (Check_Type) then
         Check_Kind := VC_Length_Check;
      else

         --  Otherwise, this is a range check

         Check_Kind := VC_Range_Check;
      end if;
   end Get_Range_Check_Info;

   ----------------------
   -- Has_Element_Expr --
   ----------------------

   function Has_Element_Expr
     (Cont   : Node_Id;
      Cursor : W_Expr_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Subp : constant Entity_Id :=
               Container_Type_To_Has_Element_Function.Element (Etype (Cont));
      Name            : constant W_Identifier_Id :=
                          To_Why_Id (Subp, Domain, Local => False);
      Call            : constant W_Expr_Id :=
                          New_Call
                            (Domain   => Domain,
                             Name     => Name,
                             Args     =>
                               (1 => Transform_Expr (Cont, Subdomain, Params),
                                2 => Cursor));
   begin
      if Domain = EW_Pred then
         return New_Relation (Domain  => EW_Pred,
                              Op_Type => EW_Bool,
                              Left    => +Call,
                              Op      => EW_Eq,
                              Right   => +True_Term);
      else
         return Call;
      end if;
   end Has_Element_Expr;

   ---------------------------
   -- Insert_Overflow_Check --
   ---------------------------

   function Insert_Overflow_Check
     (Ada_Node : Node_Id;
      T        : W_Expr_Id;
      In_Type  : Entity_Id) return W_Expr_Id
   is
      Base : constant Entity_Id := Base_Type (In_Type);

   begin
      return New_VC_Call (Domain   => EW_Prog,
                          Ada_Node => Ada_Node,
                          Name     => Prefix (S        => Full_Name (Base),
                                              W        => WNE_Range_Check_Fun,
                                              Ada_Node => Base),
                          Progs    => (1 => +T),
                          Reason   => VC_Overflow_Check);
   end Insert_Overflow_Check;

   ------------------------
   -- Insert_Range_Check --
   ------------------------

   function Insert_Range_Check
     (Expr : Node_Id;
      T    : W_Expr_Id) return W_Expr_Id
   is
      Check_Type : Entity_Id;
      Check_Kind : VC_Kind;

   begin
      --  Determine the type Check_Type, whose base type will give the bounds
      --  for the check, and whether the check is a range check or an index
      --  check.

      Get_Range_Check_Info (Expr, Check_Type, Check_Kind);

      return New_VC_Call (Domain   => EW_Prog,
                          Ada_Node => Expr,
                          Name     => Range_Check_Name (Check_Type),
                          Progs    => (1 => +T),
                          Reason   => Check_Kind);
   end Insert_Range_Check;

   ------------------------
   -- Insert_Ref_Context --
   ------------------------

   function Insert_Ref_Context
     (Params     : Transformation_Params;
      Ada_Call   : Node_Id;
      Why_Call   : W_Prog_Id;
      Nb_Of_Refs : Positive)
     return W_Prog_Id
   is
      --  This goes recursively through the out/"in out" parameters
      --  to be converted; and collects, for each of them:
      --
      --  * the name of the corresponding tmp variable;
      --  * the expression of the conversion from the actual to the tmp;
      --  * a statement sequence for the conversions back to the actual.
      --
      --  The first two are set together after that. It cannot be done
      --  during the recursive traversal, as we are building its
      --  children during the traversal and that only root nodes can have
      --  their children modified.

      Ref_Context : W_Prog_Id;
      Index       : Positive := 1;
      Tmp_Vars    : W_Identifier_Array (1 .. Nb_Of_Refs);
      Fetch       : W_Prog_Array (1 .. Nb_Of_Refs);
      Store       : constant W_Statement_Sequence_Unchecked_Id :=
                      New_Unchecked_Statement_Sequence;

      procedure Process_Arg (Formal, Actual : Node_Id);

      -----------------
      -- Process_Arg --
      -----------------

      procedure Process_Arg (Formal, Actual : Node_Id) is
      begin
         if Needs_Temporary_Ref (Actual, Formal) then
            declare
               --  Types:

               Formal_T      : constant W_Base_Type_Id :=
                                 Type_Of_Node (Formal);
               Actual_T      : constant W_Base_Type_Id :=
                                 Type_Of_Node (Actual);

               --  Variables:

               --  We should never use the Formal for the Ada_Node,
               --  because there is no real dependency here; We only
               --  use the Formal to get a sensible name.

               Tmp_Var       : constant W_Identifier_Id :=
                 New_Identifier (Ada_Node => Empty,
                                 Name     => Full_Name (Formal));
               Tmp_Var_Deref : constant W_Prog_Id :=
                                 New_Deref (Right => Tmp_Var);

               --  1/ Before the call (saving into a temporary variable):
               ----------------------------------------------------------

               --  On fetch, range checks are only needed when the formal
               --  is "in out". Disable them by using the term domain in
               --  case of "out" parameters.

               Fetch_Domain  : constant EW_Domain :=
                                 (if Ekind (Formal) in E_Out_Parameter then
                                    EW_Term
                                  else
                                    EW_Prog);

               --  Generate an expression of the form:
               --
               --    to_formal_type (from_actual_type (!actual))
               --
               --  ... with the appropriate range checks in the case of
               --  "in out" parameters:

               Fetch_Actual  : constant W_Prog_Id :=
                                 +Insert_Conversion
                                   (Domain   => Fetch_Domain,
                                    Ada_Node => Actual,
                                    Expr     =>
                                      +Transform_Expr (Actual,
                                                       EW_Prog,
                                                       Params),
                                    From     => Actual_T,
                                    To       => Formal_T);

               --  2/ After the call (storing the result):
               -------------------------------------------

               --  Generate an expression of the form:
               --
               --    to_actual_type_ (from_formal_type (!tmp_var))
               --
               --  ... with the appropriate range checks...

               Arg_Value     : constant W_Prog_Id :=
                                 +Insert_Conversion
                                   (Domain   => EW_Prog,
                                    Ada_Node => Actual,
                                    Expr     => +Tmp_Var_Deref,
                                    From     => Formal_T,
                                    To       => Actual_T);

               --  ...then store it into the actual:

               Store_Value   : constant W_Prog_Id :=
                                 New_Assignment
                                   (Ada_Node => Actual,
                                    Lvalue   => Actual,
                                    Val_Type => Type_Of_Node (Actual),
                                    Expr     => Arg_Value);
            begin
               Statement_Sequence_Append_To_Statements (Store, Store_Value);
               Tmp_Vars (Index) := Tmp_Var;
               Fetch (Index) := Fetch_Actual;
               Index := Index + 1;
            end;
         end if;
      end Process_Arg;

      procedure Iterate_Call is new
        Iterate_Call_Arguments (Process_Arg);

   --  Start of processing for Insert_Ref_Context

   begin
      Statement_Sequence_Append_To_Statements (Store, Why_Call);
      Iterate_Call (Ada_Call);

      --  Set the pieces together

      Ref_Context := +Store;
      for J in Fetch'Range loop
         Ref_Context :=
           New_Binding_Ref
             (Name    => Tmp_Vars (J),
              Def     => Fetch (J),
              Context => Ref_Context);
      end loop;

      return Ref_Context;
   end Insert_Ref_Context;

   --------------------
   -- Is_Pretty_Node --
   --------------------

   function Is_Pretty_Node (N : Node_Id) return Boolean
   is
   begin
      case Nkind (N) is
         when N_Quantified_Expression | N_And_Then |
              N_Op_And | N_If_Expression
            => return False;
         when others => return True;
      end case;
   end Is_Pretty_Node;

   ----------------------------
   -- Iterate_Call_Arguments --
   ----------------------------

   procedure Iterate_Call_Arguments (Call : Node_Id)
   is
      Params     : constant List_Id := Parameter_Associations (Call);
      Cur_Formal : Node_Id := First_Entity (Entity (Name (Call)));
      Cur_Actual : Node_Id := First (Params);
      In_Named   : Boolean := False;
   begin
      --  We have to deal with named arguments, but the frontend has
      --  done some work for us. All unnamed arguments come first and
      --  are given as-is, while named arguments are wrapped into a
      --  N_Parameter_Association. The field First_Named_Actual of the
      --  function or procedure call points to the first named argument,
      --  that should be inserted after the last unnamed one. Each
      --  Named Actual then points to a Next_Named_Actual. These
      --  pointers point directly to the actual, but Next_Named_Actual
      --  pointers are attached to the N_Parameter_Association, so to
      --  get the next actual from the current one, we need to follow
      --  the Parent pointer.
      --
      --  The Boolean In_Named states how to obtain the next actual:
      --  either follow the Next pointer, or the Next_Named_Actual of
      --  the parent.
      --  We start by updating the Cur_Actual and In_Named variables for
      --  the first parameter.

      if Nkind (Cur_Actual) = N_Parameter_Association then
         In_Named := True;
         Cur_Actual := First_Named_Actual (Call);
      end if;

      while Present (Cur_Formal) and then Present (Cur_Actual) loop
         Handle_Argument (Cur_Formal, Cur_Actual);
         Cur_Formal := Next_Formal (Cur_Formal);

         if In_Named then
            Cur_Actual := Next_Named_Actual (Parent (Cur_Actual));
         else
            Next (Cur_Actual);

            if Nkind (Cur_Actual) = N_Parameter_Association then
               In_Named := True;
               Cur_Actual := First_Named_Actual (Call);
            end if;
         end if;
      end loop;
   end Iterate_Call_Arguments;

   -------------------------
   -- Name_For_Loop_Entry --
   -------------------------

   function Name_For_Loop_Entry
     (Expr    : Node_Id;
      Loop_Id : Node_Id) return W_Identifier_Id
   is
      Result : W_Identifier_Id;

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map);
      --  Update the mapping Loop_Map with an entry for Expr if not already
      --  present, and store in Result the corresponding identifier.

      --------------
      -- Get_Name --
      --------------

      procedure Get_Name
        (Loop_Id  : Node_Id;
         Loop_Map : in out Ada_To_Why_Ident.Map) is
      begin
         pragma Unreferenced (Loop_Id);

         if not Loop_Map.Contains (Expr) then
            Loop_Map.Include (Expr, New_Temp_Identifier);
         end if;

         Result := Loop_Map.Element (Expr);
      end Get_Name;

   --  Start of Name_For_Loop_Entry

   begin
      if not Loop_Entry_Map.Contains (Loop_Id) then
         declare
            Empty_Map : Ada_To_Why_Ident.Map;
         begin
            Loop_Entry_Map.Include (Loop_Id, Empty_Map);
         end;
      end if;

      Loop_Entry_Map.Update_Element
        (Position => Loop_Entry_Map.Find (Loop_Id),
         Process  => Get_Name'Access);

      return Result;
   end Name_For_Loop_Entry;

   ------------------
   -- Name_For_Old --
   ------------------

   function Name_For_Old (N : Node_Id) return W_Identifier_Id is
   begin
      if not Old_Map.Contains (N) then
         Old_Map.Include (N, New_Temp_Identifier);
      end if;

      return Old_Map.Element (N);
   end Name_For_Old;

   ---------------------
   -- Name_For_Result --
   ---------------------

   function Name_For_Result return W_Identifier_Id is
   begin
      pragma Assert (Result_Name /= Why_Empty);
      return Result_Name;
   end Name_For_Result;

   -------------------------
   -- Needs_Temporary_Ref --
   -------------------------

   function Needs_Temporary_Ref
     (Actual : Node_Id;
      Formal : Node_Id)
     return Boolean is
   begin
      --  Temporary refs are needed for out or in out parameters that
      --  need a conversion or who are not an identifier.
      return Ekind (Formal) in E_In_Out_Parameter | E_Out_Parameter
        and then (not Eq (Etype (Actual), Etype (Formal))
                  or else not (Nkind (Actual) in N_Entity));
   end Needs_Temporary_Ref;

   --------------------
   -- New_Assignment --
   --------------------

   function New_Assignment
     (Ada_Node : Node_Id := Empty;
      Lvalue   : Node_Id;
      Val_Type : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is

      --  Here, we deal with assignment statements. In SPARK, the general form
      --  of an assignment is
      --
      --    Lvalue := Expr;
      --
      --  where Lvalue is a mix of array and record accesses. If we adopt the
      --  same notation for both, we obtain the general form
      --
      --    Prefix.Acc1.Acc2.(...).Accn := Expr;
      --
      --  where the Acc(i) are either array accesses using an index (or
      --  several indices in the multidimensional case) or record accesses
      --  using a field name.
      --
      --  Here, we generate Why code of the form
      --
      --    Prefix := Upd (Prefix, Acc1,
      --                   (Upd (Prefix.Acc1, Acc2,
      --                         Upd (..., Accn, Expr))));

      procedure Shift_Rvalue
        (N         : in out Node_Id;
         Expr      : in out W_Prog_Id;
         Expr_Type : in out Entity_Id);
      --  the input triple (N, Expr, Expr_Type) describes an assignment
      --      N := Expr
      --  where N is the Ada node for some Lvalue of the form
      --    Prefix.Acc1.(...).Acc[n-1].Accn := Expr;
      --  Expr_Type is the type in which the assignment takes place, ie. the
      --  type of Expr and of Accn.
      --  The *output* triple (N, Expr, Expr_Type) corresponds to the same
      --  assignment, but shifting the Accn to the right side and transforming
      --  it into an update. We obtain
      --    Prefix.Acc1.(...).Acc[n-1] :=
      --         Upd (Prefix.Acc1.(...).Acc[n-1], Accn, Expr)

      ------------------
      -- Shift_Rvalue --
      ------------------

      procedure Shift_Rvalue
        (N         : in out Node_Id;
         Expr      : in out W_Prog_Id;
         Expr_Type : in out Entity_Id)
      is
      begin
         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               null;

            when N_Type_Conversion =>
               declare
                  New_Type : constant Entity_Id := Etype (Expression (N));
               begin
                  N := Expression (N);
                  Expr :=
                    +Insert_Conversion
                      (Domain => EW_Prog,
                       Expr   => +Expr,
                       To     => Type_Of_Node (New_Type),
                       From   => Type_Of_Node (Expr_Type));
                  Expr_Type := New_Type;
               end;

            when N_Selected_Component | N_Indexed_Component | N_Slice =>
               declare
                  Prefix_Type : constant Entity_Id :=
                    Expected_Type_Of_Prefix (Prefix (N));
                  Prefix_Expr : constant W_Value_Id :=
                    +Transform_Expr (Domain        => EW_Prog,
                                     Expr          => Prefix (N),
                                     Expected_Type =>
                                       Type_Of_Node (Prefix_Type),
                                     Params        => Body_Params);
               begin
                  Expr :=
                    +One_Level_Update (N,
                                       +Prefix_Expr,
                                       +Expr,
                                       Prefix_Type,
                                       Expr_Type,
                                       EW_Prog,
                                       Params => Body_Params);
                  N := Prefix (N);
                  Expr_Type := Prefix_Type;
               end;

            when others =>
               Ada.Text_IO.Put_Line ("[Compute_Rvalue] kind ="
                                     & Node_Kind'Image (Nkind (N)));
               raise Not_Implemented;
         end case;
      end Shift_Rvalue;

      --  begin processing for Transform_Assignment_Statement

      Left_Side  : Node_Id := Lvalue;
      Right_Side : W_Prog_Id := Expr;
      Cur_Type   : Entity_Id := Val_Type;
   begin
      while not (Nkind (Left_Side) in N_Identifier | N_Expanded_Name) loop
         Shift_Rvalue (Left_Side, Right_Side, Cur_Type);
      end loop;
      return
        New_Assignment
          (Ada_Node => Ada_Node,
           Name     => To_Why_Id (Entity (Left_Side)),
           Value    => Right_Side);
   end New_Assignment;

   ----------------------
   -- One_Level_Access --
   ----------------------

   function One_Level_Access
     (N            : Node_Id;
      Expr         : W_Expr_Id;
      Domain       : EW_Domain;
      Params       : Transformation_Params;
      Current_Type : out W_Base_Type_Id) return W_Expr_Id
   is
   begin
      case Nkind (N) is
         when N_Selected_Component =>
            declare
               Sel_Ent : constant Entity_Id := Entity (Selector_Name (N));
               Id      : constant W_Identifier_Id := To_Why_Id (Sel_Ent);
               Rec_Ty  : constant Entity_Id :=
                 Unique_Entity (Etype (Prefix (N)));
            begin
               if Is_Access_To_Formal_Container_Capacity (N) then
                  Current_Type := Type_Of_Node (N);
                  return
                    New_Call (Ada_Node => N,
                              Domain   => Domain,
                              Name     => Id,
                              Args     => (1 => Expr));
               else
                  Current_Type :=
                    Type_Of_Node (Search_Component_By_Name (Rec_Ty, Sel_Ent));
                  return
                    New_Ada_Record_Access
                      (Ada_Node => N,
                       Domain   => Domain,
                       Name     => Expr,
                       Ty       => Rec_Ty,
                       Field    => Sel_Ent);
               end if;
            end;

         when N_Indexed_Component =>

            --  ??? Save the index in a temporary variable

            declare
               Ar      : constant Node_Id := Prefix (N);
               Dim     : constant Pos := Number_Dimensions (Type_Of_Node (Ar));
               T_Name  : constant Entity_Id := Type_Of_Node (Ar);
               Indices : W_Expr_Array :=
                  (1 .. Integer (Dim) => <>);
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               Current_Type :=
                 Type_Of_Node (Component_Type (Unique_Entity (Etype (Ar))));
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, Domain, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;

               return
                  New_Array_Access
                   (Ada_Node  => N,
                    Domain    => Domain,
                    Ty_Entity => T_Name,
                    Ar        => Expr,
                    Index     => Indices,
                    Dimension => Dim);
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Access] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;
   end One_Level_Access;

   ----------------------
   -- One_Level_Update --
   ----------------------

   function One_Level_Update
     (N           : Node_Id;
      Pref        : W_Expr_Id;
      Value       : W_Expr_Id;
      Prefix_Type : Entity_Id;
      Val_Type    : Entity_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id is
   begin
      case Nkind (N) is
         when N_Selected_Component =>

            --  The code should never update the capacity of a container by
            --  assigning to it. This is ensured by making the formal container
            --  type a private type, but keep the assertion in case.

            pragma Assert (not Is_Access_To_Formal_Container_Capacity (N));

            return New_Ada_Record_Update
              (Ada_Node => N,
               Domain   => Domain,
               Name     => Pref,
               Field    => Entity (Selector_Name (N)),
               Ty       => Prefix_Type,
               Value    => Value);

         when N_Indexed_Component =>
            declare
               Dim     : constant Pos :=
                  Number_Dimensions (Type_Of_Node (Prefix (N)));
               Indices : W_Expr_Array := (1 .. Integer (Dim) => <>);
               Cursor  : Node_Id := First (Expressions (N));
               Count   : Positive := 1;
            begin
               while Present (Cursor) loop
                  Indices (Count) :=
                     Transform_Expr
                        (Cursor, EW_Int_Type, EW_Prog, Params);
                  Count := Count + 1;
                  Next (Cursor);
               end loop;
               return
                  New_Array_Update (Ada_Node  => N,
                                    Ty_Entity => Prefix_Type,
                                    Ar        => Pref,
                                    Index     => Indices,
                                    Value     => Value,
                                    Domain    => Domain,
                                    Dimension => Dim);
            end;

         when N_Slice =>
            declare
               Prefix_Name : constant W_Identifier_Id := New_Temp_Identifier;
               Value_Name  : constant W_Identifier_Id := New_Temp_Identifier;
               Prefix_Expr : constant W_Value_Id :=
                               +Transform_Expr
                                 (Prefix (N),
                                  EW_Term,
                                  Params => Params);
               Dim         : constant Pos := Number_Dimensions (Prefix_Type);
               BT          : constant W_Base_Type_Id :=
                               +Why_Logic_Type_Of_Ada_Type (Prefix_Type);
               Result_Id   : constant W_Identifier_Id := To_Ident (WNE_Result);
               Binders     : constant W_Identifier_Array :=
                               New_Temp_Identifiers (Positive (Dim));
               Indexes     : constant W_Expr_Array := To_Exprs (Binders);
               Range_Pred  : constant W_Expr_Id :=
                               Transform_Discrete_Choice
                                 (Choice => Discrete_Range (N),
                                  Expr   => Indexes (1),
                                  Domain => EW_Pred,
                                  Params => Params);
               In_Slice_Eq : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Left_Type  => Prefix_Type,
                                  Right_Arr  => +Value_Name,
                                  Right_Type => Val_Type,
                                  Index      => Indexes,
                                  Dimension  => Dim);
               Unchanged   : constant W_Pred_Id :=
                               New_Element_Equality
                                 (Left_Arr   => +Result_Id,
                                  Left_Type  => Prefix_Type,
                                  Right_Arr  => +Prefix_Name,
                                  Right_Type => Val_Type,
                                  Index      => Indexes,
                                  Dimension  => Dim);

               --  ??? Why is the Right_Type above Val_Type and not
               --  Prefix_Type?

               Def         : constant W_Pred_Id :=
                               New_Conditional
                                 (Condition => Range_Pred,
                                  Then_Part => +In_Slice_Eq,
                                  Else_Part => +Unchanged);
               Quantif     : constant W_Expr_Id :=
                               New_Universal_Quantif
                                 (Variables => Binders,
                                  Var_Type  => +EW_Int_Type,
                                  Pred      => Def);
            begin
               return
                 New_Binding
                   (Domain => EW_Prog,
                    Name   => Prefix_Name,
                    Def    => Prefix_Expr,
                    Context =>
                      New_Binding
                        (Domain  => EW_Prog,
                         Name    => Value_Name,
                         Def     => +Value,
                         Context => +New_Simpl_Any_Prog
                           (T => +BT,
                            Pred => +Quantif)));
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[One_Level_Update] kind ="
                                  & Node_Kind'Image (Nkind (N)));
            raise Not_Implemented;
      end case;

   end One_Level_Update;

   ----------------
   -- Range_Expr --
   ----------------

   function Range_Expr
     (N           : Node_Id;
      T           : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params;
      T_Type      : W_Base_Type_OId := Why_Empty) return W_Expr_Id
   is
      Subdomain  : constant EW_Domain :=
                     (if Domain = EW_Pred then EW_Term else Domain);
      Range_Node : constant Node_Id := Get_Range (N);
      Low        : constant Node_Id := Low_Bound (Range_Node);
      High       : constant Node_Id := High_Bound (Range_Node);
      Base_Type  : W_Base_Type_Id := Base_Why_Type (Low, High);
   begin
      if T_Type /= Why_Empty then
         Base_Type := Base_Why_Type (T_Type, Base_Type);
      end if;

      return
        New_Range_Expr
          (Domain    => Domain,
           Base_Type => Base_Type,
           Low       => +Transform_Expr (Low,
                                         Base_Type,
                                         Subdomain,
                                         Params),
           High      => +Transform_Expr (High,
                                         Base_Type,
                                         Subdomain,
                                         Params),
           Expr      => T);
   end Range_Expr;

   -----------------------
   -- Reset_Map_For_Old --
   -----------------------

   procedure Reset_Map_For_Old is
   begin
      Old_Map.Clear;
   end Reset_Map_For_Old;

   -----------------------
   -- Transform_Actions --
   -----------------------

   function Transform_Actions
     (Actions : List_Id;
      Expr    : W_Expr_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id
   is
      T : W_Expr_Id;
      N : Node_Id;

      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);

   begin
      T := Expr;
      N := First (Actions);
      while Present (N) loop
         pragma Assert (Nkind (N) = N_Subtype_Declaration
                          or else
                        Nkind (N) = N_Full_Type_Declaration
                          or else
                        (Nkind (N) = N_Object_Declaration
                          and then Constant_Present (N)));

         --  Ignore type declarations in actions

         if Nkind (N) = N_Object_Declaration then
            T := New_Binding
              (Domain   => Subdomain,
               Name     =>
                 New_Identifier (Name => Full_Name (Defining_Identifier (N))),
               Def      => +Transform_Expr (Expression (N), Subdomain, Params),
               Context  => T);
         end if;

         Next (N);
      end loop;

      return T;
   end Transform_Actions;

   -----------------------------------
   -- Transform_Actions_Preparation --
   -----------------------------------

   procedure Transform_Actions_Preparation
     (Actions : List_Id;
      Params  : in out Transformation_Params)
   is
      N  : Node_Id;
      Id : W_Identifier_Id;

   begin
      N := First (Actions);
      while Present (N) loop
         pragma Assert (Nkind (N) = N_Subtype_Declaration
                          or else
                        Nkind (N) = N_Full_Type_Declaration
                          or else
                        (Nkind (N) = N_Object_Declaration
                          and then Constant_Present (N)));

         --  Ignore type declarations in actions

         if Nkind (N) = N_Object_Declaration then
            Id := New_Identifier (Name => Full_Name (Defining_Identifier (N)));

            Ada_Ent_To_Why.Insert (Params.Name_Map,
                                   Defining_Identifier (N),
                                   +Id);
         end if;

         Next (N);
      end loop;
   end Transform_Actions_Preparation;

   -------------------------
   -- Transform_Aggregate --
   -------------------------

   function Transform_Aggregate
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id) return W_Expr_Id
   is
      -----------------------
      -- Local subprograms --
      -----------------------

      procedure Get_Aggregate_Elements
        (Expr   : Node_Id;
         Values : out List_Of_Nodes.List;
         Types  : out List_Of_Nodes.List);
      --  Extract elements of the aggregate Expr that will be passed in
      --  parameter. Each element of Values is an element of the (possibly
      --  multi-dimensional) aggregate, with the corresponding type stored at
      --  the same position in Types.

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List);
      --  Generate the logic function definition for the aggregate Expr, with a
      --  suitable defining axiom:
      --
      --     function F (<params>) : <type of aggregate>
      --
      --     axiom A:
      --       forall id:<type of aggregate>. forall <params>.
      --         <proposition for the aggregate F(<params>)>

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id;
      --  Generates the proposition defining the aggregate Arr, based on a
      --  mapping between Ada nodes and corresponding Why identifiers.

      function Complete_Translation
        (Params : Transformation_Params;
         Domain : EW_Domain;
         Func   : W_Identifier_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List) return W_Expr_Id;
      --  Given a logic function Func previously defined for the aggregate,
      --  generate the actual call to Func by translating arguments Values
      --  of type Types in the context given by Params.

      --------------------------
      -- Complete_Translation --
      --------------------------

      function Complete_Translation
        (Params : Transformation_Params;
         Domain : EW_Domain;
         Func   : W_Identifier_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List) return W_Expr_Id
      is
         pragma Assert (Values.Length /= 0);

         use List_Of_Nodes;

         Cnt   : Positive;
         Value : List_Of_Nodes.Cursor;
         Typ   : List_Of_Nodes.Cursor;
         Args  : W_Expr_Array (1 .. Integer (Values.Length));

      begin
         --  Compute the arguments for the function call

         Cnt   := 1;
         Value := Values.First;
         Typ   := Types.First;
         while Value /= No_Element loop
            Args (Cnt) :=
              Transform_Expr
                (Element (Value),
                 +Why_Logic_Type_Of_Ada_Type (Element (Typ)),
                 Domain,
                 Params);
            Next (Value);
            Next (Typ);
            Cnt := Cnt + 1;
         end loop;

         --  Return the call

         return New_Call (Ada_Node => Expr,
                          Domain   => Domain,
                          Name     => Func,
                          Args     => Args);
      end Complete_Translation;

      -----------------------------
      -- Generate_Logic_Function --
      -----------------------------

      procedure Generate_Logic_Function
        (Expr   : Node_Id;
         Values : List_Of_Nodes.List;
         Types  : List_Of_Nodes.List)
      is
         pragma Assert (Values.Length /= 0);

         use List_Of_Nodes;

         Expr_Typ      : constant Entity_Id := Type_Of_Node (Expr);

         --  Generate name for the function based on the location of the
         --  aggregate.

         Name          : constant String := New_Str_Lit_Ident (Expr);
         Func          : constant W_Identifier_Id :=
                           New_Identifier (Name     => Name,
                                           Ada_Node => Expr);

         --  Predicate used to define the aggregate

         Params_No_Ref : constant Transformation_Params :=
                           (Theory      => Params.Theory,
                            File        => Params.File,
                            Phase       => Params.Phase,
                            Gen_Image   => False,
                            Ref_Allowed => False,
                            Name_Map    => Ada_Ent_To_Why.Empty_Map);

         --  Values used in calls to the aggregate function

         Ret_Type      : constant W_Primitive_Type_Id :=
                           +Why_Logic_Type_Of_Ada_Type (Expr_Typ);

         --  Arrays of binders and arguments, and mapping of nodes to names

         Call_Params   : Binder_Array (1 .. Integer (Values.Length));
         Call_Args     : W_Expr_Array (1 .. Integer (Values.Length));
         Args_Map      : Ada_Ent_To_Why.Map;

         --  Counter and iterators

         Cnt           : Positive;
         Value         : List_Of_Nodes.Cursor;
         Typ           : List_Of_Nodes.Cursor;

         --  Variables for the call, guard and proposition for the axiom

         Aggr          : W_Expr_Id;
         Call          : W_Expr_Id;
         Def_Pred      : W_Pred_Id;

         Aggr_Temp     : constant W_Identifier_Id := New_Temp_Identifier;

         --  Select file for the declarations

         Decl_File     : Why_File := Why_Files (Dispatch_Entity (Expr));

      --  Start of Generate_Logic_Function

      begin
         --  Store the logic function

         Ada_To_Why_Func.Include (Expr, +Func);

         --  Compute the parameters/arguments for the axiom/call

         Cnt   := 1;
         Value := Values.First;
         Typ := Types.First;
         while Value /= No_Element loop
            declare
               Ident : constant W_Identifier_Id := New_Temp_Identifier;
            begin
               Call_Params (Cnt) :=
                 (Ada_Node => Empty,
                  B_Name   => Ident,
                  Modifier => None,
                  B_Type   => Why_Logic_Type_Of_Ada_Type (Element (Typ)));
               Call_Args (Cnt) := +Ident;

               --  Fill in mapping from Ada nodes to Why identifiers for the
               --  generation of the proposition in the defining axiom.

               Ada_Ent_To_Why.Insert (Args_Map, Element (Value), +Ident);

               Next (Typ);
               Next (Value);
               Cnt := Cnt + 1;
            end;
         end loop;

         --  Compute the call, guard and proposition for the axiom

         Aggr :=
           New_Call (Ada_Node => Expr,
                          Domain   => EW_Term,
                          Name     => Func,
                          Args     => Call_Args);
         Call :=
           Array_Convert_To_Base
             (Ty_Entity => Etype (Expr),
              Domain    => EW_Term,
              Ar        => Aggr);

         Def_Pred :=
           New_Binding
             (Name   => Aggr_Temp,
              Def    => W_Value_Id (Call),
              Context =>
                +Transform_Array_Component_Associations
                  (Expr   => Expr,
                   Arr    => +Aggr_Temp,
                   Args   => Args_Map,
                   Params => Params_No_Ref));

         --  Generate the necessary logic function and axiom declarations

         if Params.File = Decl_File.File then
            Decl_File.Cur_Theory := Why_Empty;
         end if;
         Open_Theory
           (Decl_File, Name,
            Comment =>
              "Module for defining the value of the aggregate at "
                & (if Sloc (Expr) > 0 then
                      Build_Location_String (Sloc (Expr))
                   else "<no location>")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Emit (Decl_File.Cur_Theory,
               New_Function_Decl (Domain      => EW_Term,
                                  Name        => Func,
                                  Binders     => Call_Params,
                                  Return_Type => Ret_Type));
         Emit (Decl_File.Cur_Theory,
               New_Guarded_Axiom (Name     => To_Ident (WNE_Def_Axiom),
                                  Binders  => Call_Params,
                                  Triggers =>
                                    New_Triggers
                                      (Triggers =>
                                           (1 => New_Trigger
                                                (Terms => (1 => Aggr)))),
                                  Def      => Def_Pred));

         Close_Theory (Decl_File, Filter_Entity => Expr);
         if Params.File = Decl_File.File then
            Decl_File.Cur_Theory := Params.Theory;
         end if;
      end Generate_Logic_Function;

      ----------------------------
      -- Get_Aggregate_Elements --
      ----------------------------

      procedure Get_Aggregate_Elements
        (Expr   : Node_Id;
         Values : out List_Of_Nodes.List;
         Types  : out List_Of_Nodes.List)
      is
         Typ     : constant Entity_Id := Type_Of_Node (Expr);
         Num_Dim : constant Pos       := Number_Dimensions (Typ);

         -----------------------
         -- Local subprograms --
         -----------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id);
         --  Traverse the value Expr_Or_Association to collect desired elements

         procedure Traverse_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id);
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         -----------------------------
         -- Traverse_Value_At_Index --
         -----------------------------

         procedure Traverse_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id)
         is
            Expr : Node_Id;
         begin
            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               null;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                    Expression (Expr_Or_Association)
                  else
                    Expr_Or_Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  Traverse_Rec_Aggregate (Dim + 1, Expr);
               else
                  declare
                     Exp_Type  : constant Node_Id := Component_Type (Typ);
                  begin
                     Values.Append (Expr);
                     Types.Append (Exp_Type);
                  end;
               end if;
            end if;
         end Traverse_Value_At_Index;

         ----------------------------
         -- Traverse_Rec_Aggregate --
         ----------------------------

         procedure Traverse_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id)
         is
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Expression  : Node_Id := Nlists.First (Exprs);
            Association : Node_Id := Nlists.First (Assocs);

         begin
            while Present (Expression) loop
               Traverse_Value_At_Index (Dim, Expression);
               Next (Expression);
            end loop;

            --  Although named association is not allowed after positional
            --  association, an "others" case is allowed, and this is included
            --  in the list of associations, so we always do the following.

            while Present (Association) loop
               Traverse_Value_At_Index (Dim, Association);
               Next (Association);
            end loop;
         end Traverse_Rec_Aggregate;

         --  Start of Get_Aggregate_Elements

      begin
         Traverse_Rec_Aggregate (Dim => 1, Expr => Expr);
      end Get_Aggregate_Elements;

      --------------------------------------------
      -- Transform_Array_Component_Associations --
      --------------------------------------------

      function Transform_Array_Component_Associations
        (Expr   : Node_Id;
         Arr    : W_Expr_Id;
         Args   : Ada_Ent_To_Why.Map;
         Params : Transformation_Params) return W_Pred_Id
      is
         Typ     : constant Entity_Id := Type_Of_Node (Expr);
         Num_Dim : constant Pos := Number_Dimensions (Typ);
         Ind_Arr : array (1 .. Num_Dim) of Node_Id;
         Binders : W_Identifier_Array (1 .. Positive (Num_Dim));

         Indexes : W_Expr_Array (1 .. Positive (Num_Dim));
         --  This array contains either the identifiers for indexes in the
         --  normal translation, or the actual values of indexes in the
         --  translation for "simple" aggregates. For example, in the first
         --  case it could be:
         --     (tmp1, tmp2, tmp3)
         --  while in the second case it could be:
         --     (1, 3, 2)
         --  This allows using Constrain_Value_At_Index in both cases to get
         --  the value of the aggregate at the desired indexes.

         -----------------------
         -- Local subprograms --
         -----------------------

         type Transform_Rec_Func is access function
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Type of callback used to refer to either one of the recursive
         --  transformation functions for aggregate defined below, for use in
         --  Constrain_Value_At_Index.

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id;
         --  Return the proposition that the array at the given indices is
         --  equal to the value given in Expr_Or_Association, or else "true"
         --  for box association.

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean;
         --  Detect whether aggregate Expr has no "others" or range choices, or
         --  multiple choices in an association.

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id;
         --  Return the value for Index at Offset from Id'First

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id;
         --  Return a proposition that expresses that Index satisfies one
         --  choice in the list of choices L.

         function Transform_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Main recursive function operating over multi-dimensional array
         --  aggregates.

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id;
         --  Specialized version of Transform_Rec_Aggregate when the aggregate
         --  is simple, as defined by Is_Simple_Aggregate.

         ------------------------------
         -- Constrain_Value_At_Index --
         ------------------------------

         function Constrain_Value_At_Index
           (Dim                 : Pos;
            Expr_Or_Association : Node_Id;
            Callback            : Transform_Rec_Func) return W_Expr_Id
         is
            Expr : Node_Id;

         begin
            if Nkind (Expr_Or_Association) = N_Component_Association
              and then Box_Present (Expr_Or_Association)
            then
               return +True_Pred;
            else
               Expr :=
                 (if Nkind (Expr_Or_Association) =
                    N_Component_Association
                  then
                     Expression (Expr_Or_Association)
                  else
                     Expr_Or_Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expr) = N_Aggregate);
                  return Callback (Dim + 1, Expr);
               else
                  declare
                     Exp_Type  : constant Node_Id := Component_Type (Typ);
                     Elmt_Type : constant W_Base_Type_Id :=
                                   +Why_Logic_Type_Of_Ada_Type (Exp_Type);
                     Value     : constant W_Expr_Id :=
                                   +Ada_Ent_To_Why.Element (Args, Expr);
                     Read      : constant W_Expr_Id :=
                       New_Simple_Array_Access
                         (Ada_Node => Expr_Or_Association,
                          Domain   => EW_Term,
                          Dimension => Num_Dim,
                          Args      => Indexes & (1 => Arr));
                  begin
                     return New_Comparison
                       (Cmp       => EW_Eq,
                        Left      => Read,
                        Right     => Value,
                        Arg_Types => Elmt_Type,
                        Domain    => EW_Pred);
                  end;
               end if;
            end if;
         end Constrain_Value_At_Index;

         -------------------------
         -- Is_Simple_Aggregate --
         -------------------------

         function Is_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return Boolean
         is
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

            Is_Simple : Boolean := True;

            procedure Check_Simple (B : Boolean);
            --  Take into account the intermediate check B

            ------------------
            -- Check_Simple --
            ------------------

            procedure Check_Simple (B : Boolean) is
            begin
               Is_Simple := B and Is_Simple;
            end Check_Simple;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            while Present (Expression) loop
               --  For multi-dimensional aggregates, recurse

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;
               Next (Expression);
            end loop;

            while Present (Association) loop

               --  Check that there is only one choice, and it is neither a
               --  range not a dynamic value.

               declare
                  Only_Choice : constant Node_Id :=
                                  First (Choices (Association));
               begin
                  Check_Simple
                    (List_Length (Choices (Association)) = 1
                      and then not Discrete_Choice_Is_Range (Only_Choice)
                      and then Compile_Time_Known_Value (Only_Choice));
               end;

               --  For multi-dimensional aggregates, recurse

               Expression := Sinfo.Expression (Association);

               if Dim < Num_Dim then
                  pragma Assert (Nkind (Expression) = N_Aggregate);
                  Check_Simple (Is_Simple_Aggregate (Dim + 1, Expression));
               end if;

               Next (Association);
            end loop;

            return Is_Simple;
         end Is_Simple_Aggregate;

         ----------------------
         -- Select_Nth_Index --
         ----------------------

         function Select_Nth_Index
           (Dim    : Pos;
            Offset : Nat) return W_Expr_Id
         is
            Rng        : constant Node_Id := Get_Range (Ind_Arr (Dim));
            Low        : constant Node_Id := Low_Bound (Rng);
            First, Val : W_Expr_Id;

         begin
            if Is_Static_Expression (Low) then
               Val := New_Integer_Constant
                 (Value => Expr_Value (Low) + UI_From_Int (Offset));

            else
               First := New_Simple_Array_Attr
                 (Attr      => Attribute_First,
                  Ar        => Arr,
                  Domain    => EW_Term,
                  Dimension => Num_Dim,
                  Argument  => UI_From_Int (Dim));
               Val := New_Binary_Op
                        (Left     => First,
                         Right    =>
                          New_Integer_Constant (Value => UI_From_Int (Offset)),
                         Op       => EW_Add,
                         Op_Type  => EW_Int);
            end if;

            return Val;
         end Select_Nth_Index;

         --------------------------
         -- Select_These_Choices --
         --------------------------

         function Select_These_Choices
           (Dim : Pos;
            L   : List_Id) return W_Expr_Id
         is
            Result : W_Expr_Id := +False_Pred;
            Choice : Node_Id   := First (L);
         begin
            while Present (Choice) loop
               Result := New_Or_Expr
                 (Left   => Result,
                  Right  =>
                    Transform_Discrete_Choice
                      (Choice      => Choice,
                       Expr        => Indexes (Integer (Dim)),
                       Domain      => EW_Pred,
                       Params => Params),
                  Domain => EW_Pred);
               Next (Choice);
            end loop;
            return Result;
         end Select_These_Choices;

         -----------------------------
         -- Transform_Rec_Aggregate --
         -----------------------------

         function Transform_Rec_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id
         is
            Callback    : constant Transform_Rec_Func :=
                            Transform_Rec_Aggregate'Access;
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;
            Else_Part   : W_Expr_Id := +True_Pred;
            Assocs_Len  : Nat;

         begin
            Assocs_Len := List_Length (Assocs);
            Association :=
              (if Nlists.Is_Empty_List (Assocs) then Empty
               else Nlists.Last (Assocs));

            --  Special case for "others" choice, which must appear alone as
            --  last association. This case also deals with a single
            --  association, wich may be useful when an "others" dynamic range
            --  is represented using X'Range or X'First..X'Last or X, which
            --  should not be translated as such. Indeed, these reference
            --  variable X which is not known in the context of the proposition
            --  generated here.

            if Present (Association)
              and then
                --  case of "others" choice
                ((List_Length (Choices (Association)) = 1
                    and then
                  Nkind (First (Choices (Association))) = N_Others_Choice)
                    or else
                  --  case of a single association
                  Assocs_Len = 1)
            then
               if not Box_Present (Association) then
                  Else_Part :=
                    Constrain_Value_At_Index (Dim, Association, Callback);
               end if;
               Prev (Association);
               Assocs_Len := Assocs_Len - 1;
            end if;

            Expression :=
              (if Nlists.Is_Empty_List (Exprs) then
                  Empty
               else
                  Nlists.Last (Exprs));

            if Present (Expression) then
               pragma Assert (No (Association));

               declare
                  Elsif_Parts : W_Expr_Array
                    (1 .. Integer (List_Length (Exprs)) - 1);
               begin
                  for Offset in reverse 1 .. List_Length (Exprs) - 1 loop
                     Elsif_Parts (Integer (Offset)) := New_Elsif
                       (Domain    => EW_Pred,
                        Condition =>
                          +New_Comparison
                            (Cmp       => EW_Eq,
                             Left      => Indexes (Integer (Dim)),
                             Right     => Select_Nth_Index (Dim, Offset),
                             Arg_Types => EW_Int_Type,
                             Domain    => EW_Pred),
                        Then_Part =>
                          Constrain_Value_At_Index
                            (Dim, Expression, Callback));
                     Prev (Expression);
                  end loop;

                  return New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       +New_Comparison
                         (Cmp       => EW_Eq,
                          Left      => Indexes (Integer (Dim)),
                          Right     => Select_Nth_Index (Dim, 0),
                          Arg_Types => EW_Int_Type,
                          Domain    => EW_Pred),
                     Then_Part   =>
                       Constrain_Value_At_Index (Dim, Expression, Callback),
                     Elsif_Parts => Elsif_Parts,
                     Else_Part   => Else_Part);
               end;

            elsif Present (Association) then
               declare
                  Elsif_Parts : W_Expr_Array (1 .. Integer (Assocs_Len) - 1);
               begin
                  for Offset in reverse 1 .. Assocs_Len - 1 loop
                     Elsif_Parts (Integer (Offset)) := New_Elsif
                       (Domain    => EW_Pred,
                        Condition =>
                          +Select_These_Choices (Dim, Choices (Association)),
                        Then_Part =>
                          Constrain_Value_At_Index
                            (Dim, Association, Callback));
                     Prev (Association);
                  end loop;

                  return New_Conditional
                    (Domain      => EW_Pred,
                     Condition   =>
                       +Select_These_Choices (Dim, Choices (Association)),
                     Then_Part   =>
                       Constrain_Value_At_Index
                         (Dim, Association, Callback),
                     Elsif_Parts => Elsif_Parts,
                     Else_Part   => Else_Part);
               end;

            else
               return Else_Part;
            end if;
         end Transform_Rec_Aggregate;

         ------------------------------------
         -- Transform_Rec_Simple_Aggregate --
         ------------------------------------

         function Transform_Rec_Simple_Aggregate
           (Dim  : Pos;
            Expr : Node_Id) return W_Expr_Id
         is
            Callback    : constant Transform_Rec_Func :=
                            Transform_Rec_Simple_Aggregate'Access;
            Exprs       : constant List_Id := Expressions (Expr);
            Assocs      : constant List_Id := Component_Associations (Expr);
            Association : Node_Id;
            Expression  : Node_Id;

         begin
            Expression  := Nlists.First (Exprs);
            Association := Nlists.First (Assocs);

            if Present (Expression) then
               pragma Assert (No (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Exprs)));
               begin
                  for Offset in 1 .. List_Length (Exprs) loop
                     Indexes (Integer (Dim)) :=
                       Select_Nth_Index (Dim, Offset - 1);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Expression, Callback);
                     Next (Expression);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;

            else
               pragma Assert (Present (Association));

               declare
                  Conjuncts : W_Expr_Array
                    (1 .. Integer (List_Length (Assocs)));
               begin
                  for Offset in 1 .. List_Length (Assocs) loop
                     pragma Assert (List_Length (Choices (Association)) = 1);
                     Indexes (Integer (Dim)) :=
                       Transform_Expr (Expr          =>
                                         First (Choices (Association)),
                                       Expected_Type => EW_Int_Type,
                                       Domain        => EW_Term,
                                       Params        => Params);
                     Conjuncts (Integer (Offset)) :=
                       Constrain_Value_At_Index (Dim, Association, Callback);
                     Next (Association);
                  end loop;

                  return New_And_Expr (Domain    => EW_Pred,
                                       Conjuncts => Conjuncts);
               end;
            end if;
         end Transform_Rec_Simple_Aggregate;

      --  Start of Transform_Array_Component_Associations

      begin
         --  Fill the array of index nodes

         Ind_Arr (1) := First_Index (Typ);
         for Dim in 2 .. Num_Dim loop
            Ind_Arr (Dim) := Next_Index (Ind_Arr (Dim - 1));
         end loop;

         --  Define index variables

         for J in 1 .. Integer (Num_Dim) loop
            Binders (J) := New_Temp_Identifier;
            Indexes (J) := +Binders (J);
         end loop;

         --  Create the proposition defining the aggregate

         if Is_Simple_Aggregate (Dim => 1, Expr => Expr) then
            return +Transform_Rec_Simple_Aggregate (Dim => 1, Expr => Expr);
         else
            return New_Universal_Quantif
              (Variables => Binders,
               Var_Type  => +EW_Int_Type,
               Pred      => +Transform_Rec_Aggregate (Dim => 1, Expr => Expr));
         end if;
      end Transform_Array_Component_Associations;

      --  Elements of the aggregate

      Values : List_Of_Nodes.List;
      Types  : List_Of_Nodes.List;

   --  Start of Transform_Aggregate

   begin
      --  Get the aggregate elements that should be passed in parameter

      Get_Aggregate_Elements (Expr, Values, Types);

      --  If not done already, generate the logic function

      if not Ada_To_Why_Func.Contains (Expr) then
         Generate_Logic_Function (Expr, Values, Types);
      end if;

      --  Retrieve the logic function previously generated, and call it on the
      --  appropriate parameters.

      declare
         Func : constant W_Identifier_Id := +Ada_To_Why_Func.Element (Expr);
      begin
         return Complete_Translation (Params, Domain, Func, Values, Types);
      end;
   end Transform_Aggregate;

   ---------------------
   -- Transform_Slice --
   ---------------------

   function Transform_Slice
     (Params       : Transformation_Params;
      Domain       : EW_Domain;
      Expr         : Node_Id) return W_Expr_Id
   is
      Prefx      : constant Node_Id := Sinfo.Prefix (Expr);
      Range_N     : constant Node_Id := Get_Range (Discrete_Range (Expr));
      Low         : constant Node_Id := Low_Bound (Range_N);
      High        : constant Node_Id := High_Bound (Range_N);
      Tmp_Low     : constant W_Identifier_Id := New_Temp_Identifier;
      Tmp_Pre     : constant W_Identifier_Id := New_Temp_Identifier;
      Array_Base  : constant Why_Name_Enum := Ada_Array_Name (1);
      Shift       : constant W_Expr_Id :=
        New_Binary_Op
          (Op_Type => EW_Int,
           Op      => EW_Substract,
           Left    => +Tmp_Low,
           Right   =>
             New_Record_Access
               (Name  => +Tmp_Pre,
                Field => Prefix (Array_Base, WNE_Array_First_Field)));
      New_Offset  : constant W_Expr_Id :=
        New_Binary_Op
          (Op_Type => EW_Int,
           Op      => EW_Add,
           Left    =>
             New_Record_Access
               (Name => +Tmp_Pre,
                Field =>
                Prefix (Array_Base, WNE_Array_Offset)),
           Right  => Shift);
      Updates     : constant W_Field_Association_Array :=
        (1 =>
           New_Field_Association
             (Field  => Prefix (Array_Base, WNE_Array_First_Field),
              Value  => +Tmp_Low,
              Domain => Domain),
         2 =>
           New_Field_Association
             (Field  => Prefix (Array_Base, WNE_Array_Last_Field),
              Value  => Transform_Expr (High, EW_Int_Type, Domain, Params),
              Domain => Domain),
         3 =>
           New_Field_Association
             (Field  => Prefix (Array_Base, WNE_Array_Offset),
              Value  => New_Offset,
              Domain => Domain));
   begin
      return
        New_Binding
          (Domain  => Domain,
           Name    => Tmp_Pre,
           Def     => +Transform_Expr (Prefx, EW_Array_Type, Domain, Params),
           Context =>
             New_Binding
               (Domain  => Domain,
                Name    => Tmp_Low,
                Def     => +Transform_Expr (Low, EW_Int_Type, Domain, Params),
                Context =>
                  New_Record_Update
                    (Name    => +Tmp_Pre,
                     Updates => Updates)));
   end Transform_Slice;

   ------------------------------------
   -- Transform_Assignment_Statement --
   ------------------------------------

   function Transform_Assignment_Statement (Stmt : Node_Id) return W_Prog_Id
   is
      Lvalue   : constant Node_Id := Name (Stmt);
      Exp_Entity : constant Entity_Id := Expected_Type_Of_Prefix (Lvalue);
   begin
      return
        New_Assignment
          (Ada_Node => Stmt,
           Lvalue   => Lvalue,
           Val_Type => Exp_Entity,
           Expr     =>
             +Transform_Expr (Expression (Stmt),
                              EW_Abstract (Exp_Entity),
                              EW_Prog,
                              Params => Body_Params));
   end Transform_Assignment_Statement;

   -----------------------------
   -- Transform_Attribute_Old --
   -----------------------------

   function Transform_Attribute_Old
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
   begin
      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred then
         return New_Relation
           (Ada_Node => Expr,
            Domain   => EW_Pred,
            Op_Type  => EW_Bool,
            Left     => +Transform_Attribute_Old (Expr, EW_Term, Params),
            Right    => +True_Term,
            Op       => EW_Eq);
      elsif Params.Phase in Generate_VCs then
         return +Name_For_Old (Expr);
      else
         return New_Old (Expr   => Transform_Expr (Expr, Domain, Params),
                         Domain => Domain);
      end if;
   end Transform_Attribute_Old;

   --------------------
   -- Transform_Attr --
   --------------------

   function Transform_Attr
     (Expr               : Node_Id;
      Domain             : EW_Domain;
      Current_Type       : out W_Base_Type_Id;
      Params             : Transformation_Params) return W_Expr_Id
   is
      Aname   : constant Name_Id := Attribute_Name (Expr);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);
      Var     : constant Node_Id      := Prefix (Expr);
      T       : W_Expr_Id;
   begin
      Current_Type := Type_Of_Node (Expr);
      case Attr_Id is
         when Attribute_Result =>
            if Params.Phase in Generate_VCs | Generate_For_Body then
               T :=
                 New_Deref
                   (Ada_Node => Expr,
                    Right    => Name_For_Result);
            else
               T := +To_Ident (WNE_Result);
            end if;

         when Attribute_Old =>
            T := Transform_Attribute_Old (Var, Domain, Params);

         when Attribute_Pred | Attribute_Succ =>
            declare
               Op     : constant EW_Binary_Op :=
                          (if Attr_Id = Attribute_Succ then
                             EW_Add
                           else
                             EW_Substract);
               Old    : W_Expr_Id;
               Offset : W_Expr_Id;
               A_Type : constant Entity_Id := Etype (Var);
               W_Type : EW_Scalar;
            begin
               case Ekind (Etype (Var)) is
                  when Discrete_Kind =>
                     if A_Type = Standard_Boolean then
                        W_Type := EW_Bool;
                        Ada.Text_IO.Put_Line
                          ("[Transform_Attr] boolean"
                           & Attribute_Id'Image (Attr_Id));
                        raise Not_Implemented;
                     else
                        W_Type := EW_Int;
                        Offset := New_Integer_Constant (Value => Uint_1);
                     end if;

                  when Float_Kind =>
                     W_Type := EW_Real;

                     --  ??? This is not strictly correct; F'Succ (A) is
                     --  usually different from A + F'Succ (0.0). But the
                     --  correct computation will be much more complicated;
                     --  and, as we map floating points to reals, our model
                     --  is quite loose anyway.

                     Offset :=
                       New_Real_Constant
                         (Value =>
                            Eval_Fat.Succ
                              (Root_Type (A_Type),
                               Ureal_0));

                  when Fixed_Point_Kind =>
                     W_Type := EW_Real;
                     Offset :=
                       New_Real_Constant (Value => Small_Value (A_Type));

                  when others =>
                     --  All possible cases should have been handled
                     --  before this point.
                     pragma Assert (False);
                     null;
               end case;

               Old :=
                 Transform_Expr
                   (First (Expressions (Expr)),
                    Why_Types (W_Type),
                    Domain,
                    Params);

               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Left     => Old,
                    Right    => Offset,
                    Op       => Op,
                    Op_Type  => W_Type);
               Current_Type := Why_Types (W_Type);
            end;

         when Attribute_Pos =>
            T := Transform_Expr (First (Expressions (Expr)),
                                 EW_Int_Type,
                                 Domain,
                                 Params);
            Current_Type := EW_Int_Type;

         when Attribute_Val =>
            declare
               Val_Type : constant W_Base_Type_Id :=
                 Type_Of_Node (Base_Type (Entity (Var)));
            begin
               T := Transform_Expr (First (Expressions (Expr)),
                                    Val_Type,
                                    Domain,
                                    Params);
               Current_Type := Val_Type;
            end;

         when Attribute_First | Attribute_Last | Attribute_Length =>
            case Ekind (Unique_Entity (Etype (Var))) is
               when Array_Kind =>

                  --  Array_Type'First

                  if Nkind (Var) in N_Identifier | N_Expanded_Name
                    and then Is_Type (Entity (Var))
                  then
                     T := New_Attribute_Expr
                       (Etype (First_Index (Entity (Var))),
                        Attr_Id);
                  else
                     T :=
                       New_Array_Attr
                         (Attr_Id,
                          Etype (Var),
                          Transform_Expr (Var, Domain, Params),
                          Domain,
                          Number_Dimensions (Type_Of_Node (Var)),
                          (if Present (Expressions (Expr)) then
                             Expr_Value (First (Expressions (Expr)))
                           else Uint_1));
                  end if;
                  Current_Type := EW_Int_Type;

               when Discrete_Kind | Real_Kind =>
                  T := New_Attribute_Expr (Etype (Var), Attr_Id);
                  Current_Type :=
                    (if Ekind (Etype (Var)) in Discrete_Kind
                     then EW_Int_Type else EW_Real_Type);

               when others =>
                  --  All possible cases should have been handled
                  --  before this point.
                  pragma Assert (False);
                  null;
            end case;

         when Attribute_Loop_Entry =>
            Loop_Entry : declare
               Arg     : constant Node_Id := First (Expressions (Expr));
               Loop_Id : Entity_Id;

            begin
               --  The loop to which attribute Loop_Entry applies is either
               --  identified explicitly in argument, or, if Loop_Entry takes
               --  no arguments, it is the innermost enclosing loop.

               if Present (Arg) then
                  Loop_Id := Entity (Arg);
               else
                  Loop_Id :=
                    Entity (Identifier (Innermost_Enclosing_Loop (Expr)));
               end if;

               pragma Assert (Domain /= EW_Pred
                               and then Params.Phase in Generate_VCs);

               T := +Name_For_Loop_Entry (Var, Loop_Id);
            end Loop_Entry;

         when Attribute_Modulus =>
            T := New_Attribute_Expr (Etype (Var), Attr_Id);
            Current_Type := EW_Int_Type;

         when Attribute_Mod =>
            T :=
              New_Call (Ada_Node => Expr,
                        Domain   => Domain,
                        Name     => To_Ident (WNE_Integer_Mod),
                        Args     =>
                          (1 => Transform_Expr (First (Expressions (Expr)),
                                                EW_Int_Type,
                                                Domain,
                                                Params),
                           2 =>
                           New_Attribute_Expr
                              (Etype (Var), Attribute_Modulus)));
            Current_Type := EW_Int_Type;

         when Attribute_Image =>

            --  We generate the expression String.to_string (image_func (expr))

            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     => +New_Attribute_Expr
                             (Etype (Var), Attr_Id),
                           Args     =>
                             (1 => Transform_Expr (First (Expressions (Expr)),
                                                   Base_Why_Type (Var),
                                                   Domain,
                              Params)));
            T := New_Call (Ada_Node => Expr,
                           Domain   => Domain,
                           Name     =>
                           New_Identifier
                             (Ada_Node => Standard_String,
                              Context  => Full_Name (Standard_String),
                              Name     => "to_string"),
                           Args     => (1 => T));

            Current_Type := +Why_Logic_Type_Of_Ada_Type (Standard_String);

         when Attribute_Value =>
            declare
               Why_Str : constant W_Base_Type_Id :=
                           +Why_Logic_Type_Of_Ada_Type (Standard_String);
               Arg     : constant W_Expr_Id :=
                           Transform_Expr (First (Expressions (Expr)),
                                           Why_Str,
                                           Domain,
                                           Params);
               Func    : constant W_Identifier_Id :=
                           +New_Attribute_Expr (Etype (Var), Attr_Id);
            begin
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     =>
                      New_Identifier
                        (Ada_Node => Standard_String,
                         Context  => Full_Name (Standard_String),
                         Name     => "from_string"),
                    Args     => (1 => Arg));
               if Domain = EW_Prog then
                  T := New_VC_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => To_Program_Space (Func),
                     Progs    => (1 => T),
                     Reason   => VC_Precondition);
               else
                  T := New_Call
                    (Ada_Node => Expr,
                     Domain   => Domain,
                     Name     => Func,
                     Args     => (1 => T));
               end if;
               Current_Type := Base_Why_Type (Var);
            end;

         when Attribute_Ceiling    |
              Attribute_Floor      |
              Attribute_Rounding   |
              Attribute_Truncation =>
            declare
               Arg  : constant W_Expr_Id :=
                        Transform_Expr (First (Expressions (Expr)),
                                        EW_Real_Type,
                                        Domain,
                                        Params);
               Attr_Name : constant Why_Name_Enum :=
                             (if Attr_Id = Attribute_Ceiling then
                                WNE_Real_Ceil
                              elsif Attr_Id = Attribute_Floor then
                                WNE_Real_Floor
                              elsif Attr_Id = Attribute_Rounding then
                                WNE_Real_Round
                              else WNE_Real_Truncate);
               Func : constant W_Identifier_Id := To_Ident (Attr_Name);
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg));
               Current_Type := EW_Int_Type;
            end;

         when Attribute_Min | Attribute_Max =>
            declare
               Arg1 : constant W_Expr_Id :=
                 Transform_Expr (First (Expressions (Expr)),
                                 EW_Int_Type,
                                 Domain,
                                 Params);
               Arg2 : constant W_Expr_Id :=
                 Transform_Expr (Next (First (Expressions (Expr))),
                                 EW_Int_Type,
                                 Domain,
                                 Params);
               Attr_Name : constant Why_Name_Enum :=
                             (if Attr_Id = Attribute_Min then
                                WNE_Integer_Min
                              else WNE_Integer_Max);
               Func : constant W_Identifier_Id := To_Ident (Attr_Name);
            begin
               T := New_Call (Ada_Node => Expr,
                              Domain   => Domain,
                              Name     => Func,
                              Args     => (1 => Arg1, 2 => Arg2));
               Current_Type := EW_Int_Type;
            end;

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Attr] id ="
                                  & Attribute_Id'Image (Attr_Id));
            raise Not_Implemented;
      end case;
      return T;
   end Transform_Attr;

   ---------------------
   -- Transform_Binop --
   ---------------------

   function Transform_Binop (Op : N_Binary_Op) return EW_Binary_Op is
   begin
      case Op is
         when N_Op_Add      => return EW_Add;
         when N_Op_Subtract => return EW_Substract;
         when N_Op_Divide   => return EW_Divide;
         when N_Op_Multiply => return EW_Multiply;
         when N_Op_Concat | N_Op_Expon => raise Program_Error;
         when others => raise Program_Error;
      end case;
   end Transform_Binop;

   -------------------------------
   -- Transform_Block_Statement --
   -------------------------------

   function Transform_Block_Statement (N : Node_Id) return W_Prog_Id
   is
      Core : constant W_Prog_Id :=
        Transform_Statements_And_Declarations
          (Statements (Handled_Statement_Sequence (N)));
   begin
      if Present (Declarations (N)) then
         return Transform_Declarations_Block (Declarations (N), Core);
      else
         return Core;
      end if;
   end Transform_Block_Statement;

   --------------------------
   -- Transform_Compare_Op --
   --------------------------

   function Transform_Compare_Op (Op : N_Op_Compare) return EW_Relation is
   begin
      case Op is
         when N_Op_Gt => return EW_Gt;
         when N_Op_Lt => return EW_Lt;
         when N_Op_Eq => return EW_Eq;
         when N_Op_Ge => return EW_Ge;
         when N_Op_Le => return EW_Le;
         when N_Op_Ne => return EW_Ne;
      end case;
   end Transform_Compare_Op;

   ---------------------------
   -- Transform_Declaration --
   ---------------------------

   function Transform_Declaration (Decl : Node_Id) return W_Prog_Id is

      function Local_Assume_Of_Scalar_Subtype
        (Params : Transformation_Params;
         Ent    : Entity_Id;
         Base   : Entity_Id) return W_Prog_Id;
      --  Local wrapper on Assume_Of_Scalar_Subtype

      function Get_Base_Type (N : Node_Id) return Entity_Id;
      --  Return the base type when N is the node of a (sub-)type
      --  declaration which requires a check.
      --  Return Empty otherwise.

      ------------------------------------
      -- Local_Assume_Of_Scalar_Subtype --
      ------------------------------------

      function Local_Assume_Of_Scalar_Subtype
        (Params : Transformation_Params;
         Ent    : Entity_Id;
         Base   : Entity_Id) return W_Prog_Id
      is
      begin

         --  If the range is not static, we need to generate a check that
         --  the subtype declaration is valid; otherwise, the frontend has
         --  done it for us already

         if not Is_Static_Range (Get_Range (Ent)) then
            return Assume_Of_Scalar_Subtype (Params, Ent, Base);
         else
            return New_Void;
         end if;
      end Local_Assume_Of_Scalar_Subtype;

      -------------------
      -- Get_Base_Type --
      -------------------

      function Get_Base_Type (N : Node_Id) return Entity_Id
      is
         Ent : constant Entity_Id := Defining_Identifier (N);
      begin

         --  Full type declarations can only require checks when they are
         --  scalar types, and then only when the range is non-static.
         if Nkind (N) = N_Full_Type_Declaration then
            if Ekind (Ent) in Scalar_Kind then
               if Is_Static_Range (Get_Range (Ent)) then
                  return Empty;
               end if;
            end if;
            declare
               T_Def : constant Node_Id := Type_Definition (N);
            begin
               case Nkind (T_Def) is
                  when N_Subtype_Indication =>
                     return Entity (Subtype_Mark (T_Def));

                  when N_Derived_Type_Definition =>
                     declare
                        S : constant Node_Id := Subtype_Indication (T_Def);
                     begin
                        if Nkind (S) = N_Subtype_Indication then
                           return Entity (Subtype_Mark (S));
                        else
                           return Entity (S);
                        end if;
                     end;

                  when others =>
                     return Empty;

               end case;
            end;
         else
            declare
               S : constant Node_Id := Subtype_Indication (N);
            begin
               if Nkind (S) = N_Subtype_Indication then
                  return Entity (Subtype_Mark (S));
               else
                  return Entity (S);
               end if;
            end;
         end if;
      end Get_Base_Type;

      R : W_Prog_Id := New_Void;

   --  Start of Transform_Declaration

   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>
            R := Assignment_Of_Obj_Decl (Decl);

         when N_Subtype_Declaration | N_Full_Type_Declaration =>
            declare
               Ent  : constant Entity_Id :=
                 Unique_Entity (Defining_Identifier (Decl));
               Base : constant Entity_Id := Get_Base_Type (Decl);
            begin
               if Present (Base) then
                  case Ekind (Ent) is
                     when Scalar_Kind =>
                        R := Local_Assume_Of_Scalar_Subtype
                          (Body_Params, Ent, Base);

                     when Array_Kind =>
                        declare
                           Index      : Node_Id   := First_Index (Ent);
                           Index_Base : Entity_Id := First_Index (Base);
                        begin
                           while Present (Index) loop
                              R := Sequence (Local_Assume_Of_Scalar_Subtype
                                              (Body_Params,
                                               Etype (Index),
                                               Etype (Index_Base)), R);
                              Next (Index);
                              Next (Index_Base);
                           end loop;
                        end;

                     when Record_Kind =>
                        null;

                     when others =>
                        Ada.Text_IO.Put_Line
                          ("[Transform_Declarations_Block] ekind ="
                           & Entity_Kind'Image (Ekind (Ent)));
                        raise Not_Implemented;
                  end case;
               end if;
            end;

         when others =>
            null;
      end case;
      return R;
   end Transform_Declaration;

   ----------------------------------
   -- Transform_Declarations_Block --
   ----------------------------------

   function Transform_Declarations_Block (L : List_Id; Core : W_Prog_Id)
      return W_Prog_Id
   is
      Cur_Decl : Node_Id := Last (L);
      R        : W_Prog_Id := Core;
   begin
      while Present (Cur_Decl) loop
         R := Sequence (Transform_Declaration (Cur_Decl), R);
         Prev (Cur_Decl);
      end loop;
      return R;
   end Transform_Declarations_Block;

   -------------------------------
   -- Transform_Discrete_Choice --
   -------------------------------

   function Transform_Discrete_Choice
     (Choice      : Node_Id;
      Expr        : W_Expr_Id;
      Domain      : EW_Domain;
      Params      : Transformation_Params) return W_Expr_Id
   is
      Subdomain : constant EW_Domain :=
                    (if Domain = EW_Pred then EW_Term else Domain);
      Is_Range  : constant Boolean := Discrete_Choice_Is_Range (Choice);

   begin
      if Nkind (Choice) = N_Others_Choice then
         return New_Literal (Domain => Domain, Value => EW_True);
      elsif Is_Range then
         return Range_Expr (Choice, Expr, Domain, Params, EW_Int_Type);
      else
         return New_Comparison
           (Cmp       => EW_Eq,
            Left      => Expr,
            Right     => Transform_Expr (Expr          => Choice,
                                         Expected_Type => EW_Int_Type,
                                         Domain        => Subdomain,
                                         Params        => Params),
            Arg_Types => EW_Int_Type,
            Domain    => Domain);
      end if;
   end Transform_Discrete_Choice;

   --------------------------------
   -- Transform_Discrete_Choices --
   --------------------------------

   function Transform_Discrete_Choices
     (Case_N       : Node_Id;
      Matched_Expr : W_Expr_Id;
      Cond_Domain  : EW_Domain;
      Params       : Transformation_Params) return W_Expr_Id
   is
      Cur_Choice : Node_Id   := First (Sinfo.Discrete_Choices (Case_N));
      C          : W_Expr_Id := New_Literal (Domain => Cond_Domain,
                                             Value  => EW_False);
   begin
      while Present (Cur_Choice) loop
         C := New_Or_Else_Expr
           (C,
            Transform_Discrete_Choice (Choice      => Cur_Choice,
                                       Expr        => Matched_Expr,
                                       Domain      => Cond_Domain,
                                       Params      => Params),
            Cond_Domain);
         Next (Cur_Choice);
      end loop;
      return C;
   end Transform_Discrete_Choices;

   ----------------------------
   -- Transform_Enum_Literal --
   ----------------------------

   function Transform_Enum_Literal
     (Expr         : Node_Id;
      Enum         : Entity_Id;
      Current_Type : out W_Base_Type_Id;
      Domain       : EW_Domain)
      return W_Expr_Id is
   begin
      --  Deal with special cases: True/False for boolean values

      if Enum = Standard_True then
         Current_Type := Why_Types (EW_Bool);
         return New_Literal (Value => EW_True,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      if Enum = Standard_False then
         Current_Type := Why_Types (EW_Bool);
         return New_Literal (Value => EW_False,
                             Domain => Domain,
                             Ada_Node => Standard_Boolean);
      end if;

      --  In the case of a subtype of an enumeration, we need to insert a
      --  conversion. We do so here by modifying the Current_Type; the
      --  conversion itself will be inserted by Transform_Expr.

      Current_Type := EW_Int_Type;
      return New_Integer_Constant
               (Ada_Node => Expr,
                Value    => Enumeration_Pos (Enum));
   end Transform_Enum_Literal;

   --------------------
   -- Transform_Expr --
   --------------------

   function Transform_Expr
     (Expr          : Node_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      T                     : W_Expr_Id;
      Current_Type          : W_Base_Type_Id := Type_Of_Node (Expr);
      Pretty_Label          : W_Identifier_Id := Why_Empty;
      Local_Params          : Transformation_Params := Params;
   begin

      --  We check whether we need to generate a pretty printing label. If we
      --  do, we set the corresponding flag to "False" so that the label is not
      --  printed for subterms.

      if Domain = EW_Pred
        and then Local_Params.Gen_Image
        and then Is_Pretty_Node (Expr) then
         Pretty_Label := New_Pretty_Label (Expr);
         Local_Params.Gen_Image := False;
      end if;

      --  Expressions that cannot be translated to predicates directly are
      --  translated to (boolean) terms, and compared to "True"

      if Domain = EW_Pred and then
         not (Nkind (Expr) in N_Op_Compare | N_Op_Not | N_Op_And | N_And_Then
         | N_Op_Or | N_Or_Else | N_In | N_If_Expression |
         N_Quantified_Expression | N_Case_Expression) and then
         not (Nkind (Expr) in N_Identifier | N_Expanded_Name and then
              Ekind (Entity (Expr)) in E_Enumeration_Literal and then
              (Entity (Expr) = Standard_True or else
               Entity (Expr) = Standard_False))
      then
         T :=
           New_Relation
             (Ada_Node => Expr,
              Domain   => EW_Pred,
              Op_Type  => EW_Bool,
              Left     =>
              +Transform_Expr (Expr, EW_Bool_Type, EW_Term, Local_Params),
              Right    => +True_Prog,
              Op       => EW_Eq);
      elsif Domain /= EW_Pred and then
        Is_Discrete_Type (Etype (Expr)) and then
        Compile_Time_Known_Value (Expr) then

         --  Optimization: if we have a discrete value that is statically
         --  known, use the static value.

         T :=
           New_Integer_Constant (Ada_Node => Expr,
                                 Value    => Expr_Value (Expr));
         Current_Type := EW_Int_Type;
      else
         case Nkind (Expr) is
         when N_Aggregate =>
            declare
               Expr_Type : constant Entity_Id := Type_Of_Node (Expr);
            begin
               if Is_Record_Type (Expr_Type) then
                  pragma Assert (No (Expressions (Expr)));
                  T :=
                     New_Record_Aggregate
                      (Associations =>
                           Transform_Record_Component_Associations
                         (Domain,
                          Expr_Type,
                          Component_Associations (Expr),
                          Local_Params));
                  Current_Type := EW_Abstract (Expr_Type);
               else
                  pragma Assert
                     (Is_Array_Type (Expr_Type) or else
                      Is_String_Type (Expr_Type));
                  T := Transform_Aggregate (Local_Params, Domain, Expr);
                  Current_Type := EW_Abstract (Expr_Type);
               end if;
            end;

         when N_Slice =>
            T := Transform_Slice (Local_Params, Domain, Expr);
            Current_Type := EW_Array_Type;

         when N_Integer_Literal =>
            T :=
              New_Integer_Constant
                (Ada_Node => Expr,
                 Value    => Intval (Expr));
            Current_Type := EW_Int_Type;

         --  Note: although the original node for a real literal might be
         --  closer to the source code expression of the value, this original
         --  node should not be used for transforming the node into Why.
         --  Indeed, a source float literal in Ada might not be representable
         --  in machine, in which case the frontend rewrites the value into a
         --  machine representable value (respecting the Ada RM rules, so
         --  getting the closest representable floating-point value).

         --  The procedure printing this node in Why takes care of putting the
         --  value in a suitable form for provers. In particular, we want to
         --  avoid printing divisions between real numbers, which provers don't
         --  handle well, even when the division can be expressed exactly as a
         --  decimal number.

         when N_Real_Literal =>
            T := New_Real_Constant (Ada_Node => Expr,
                                    Value    => Realval (Expr));
            Current_Type := EW_Real_Type;

         when N_Character_Literal =>

            T :=
              New_Integer_Constant (Ada_Node => Expr,
                                    Value    => Char_Literal_Value (Expr));
            Current_Type := EW_Int_Type;

         --  Deal with identifiers:
         --  * Enumeration literals: deal with special cases True and
         --    False, otherwise such literals are just constants
         --  * local variables are always references
         --  * global constants are logics in Why
         --  * global mutable variables are references
         --  * loop parameters are always mutable, and of type int

         when N_String_Literal =>
            declare
               Val : constant String_Id := Strval (Expr);
            begin
               if not (Strlit_To_Why_Term.Contains (Val)) then
                  Transform_String_Literal (Local_Params, Expr);
               end if;
               T := +Strlit_To_Why_Term.Element (Val);
               Current_Type := Strlit_To_Why_Type.Element (Val);
            end;

         when N_Identifier | N_Expanded_Name =>
            T := Transform_Identifier (Local_Params, Expr,
                                       Unique_Entity (Entity (Expr)),
                                       Domain, Current_Type);

         when N_Op_Compare =>
            declare
               Left      : constant Node_Id := Left_Opnd (Expr);
               Right     : constant Node_Id := Right_Opnd (Expr);
               BT        : constant W_Base_Type_Id :=
                             Base_Why_Type (Left, Right);
               Subdomain : constant EW_Domain :=
                             (if Domain = EW_Pred then EW_Term else Domain);
               Left_Arg  : constant W_Expr_Id :=
                             Transform_Expr (Left, BT, Subdomain,
                                             Local_Params);
               Right_Arg : constant W_Expr_Id :=
                             Transform_Expr (Right, BT, Subdomain,
                                             Local_Params);
            begin
               if Is_Array_Type (Etype (Left)) then
                  T := New_Call
                    (Ada_Node => Expr,
                     Domain   => Subdomain,
                     Name     =>
                       Prefix
                         (Ada_Node => Etype (Left),
                          S        =>
                            To_String
                              (Ada_Array_Name
                                   (Number_Dimensions (Type_Of_Node (Left)))),
                          W        => WNE_Bool_Eq),
                                 Args     =>
                                   (1 => Left_Arg,
                                    2 => Right_Arg));
                  if Domain = EW_Pred then
                     T := New_Comparison
                       (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                        Left      => T,
                        Right     => New_Literal (Domain => Subdomain,
                                                  Value  => EW_True),
                        Arg_Types => EW_Bool_Type,
                        Domain    => Domain);
                  end if;
               elsif Is_Record_Type (Etype (Left)) then
                  pragma Assert (Root_Record_Type (Etype (Left)) =
                                   Root_Record_Type (Etype (Right)));
                  pragma Assert (Root_Record_Type (Etype (Left)) =
                                   Get_Ada_Node (+BT));
                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Subdomain,
                       Name     =>
                         Prefix (Ada_Node => Get_Ada_Node (+BT),
                                 S        => Full_Name (Get_Ada_Node (+BT)),
                                 W        => WNE_Bool_Eq),
                       Args     => (1 => Left_Arg,
                                    2 => Right_Arg));
                  if Domain = EW_Pred then
                     T := New_Comparison
                       (Cmp       => EW_Eq,
                        Left      => T,
                        Right     => New_Literal (Domain => Subdomain,
                                                  Value  => EW_True),
                        Arg_Types => EW_Bool_Type,
                        Domain    => Domain);
                  end if;
               else
                  T := New_Comparison
                    (Cmp       => Transform_Compare_Op (Nkind (Expr)),
                     Left      => Left_Arg,
                     Right     => Right_Arg,
                     Arg_Types => BT,
                     Domain    => Domain);
               end if;
               Current_Type := EW_Bool_Type;
            end;

         when N_Op_Minus =>
            --  unary minus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T :=
                 New_Unary_Op
                   (Ada_Node => Expr,
                    Op       => EW_Minus,
                    Right    =>
                    +Transform_Expr (Right, Current_Type, Domain,
                     Local_Params),
                    Op_Type  => Get_Base_Type (Current_Type));
               T := Apply_Modulus (Etype (Expr), T, Domain);
            end;

         when N_Op_Plus =>
            --  unary plus
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T := Transform_Expr (Right, Current_Type, Domain, Local_Params);
            end;

         when N_Op_Abs =>
            declare
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Right);
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Abs (Get_Base_Type (Current_Type)),
                    Args    =>
                      (1 => Transform_Expr (Right, Current_Type,
                       Domain, Local_Params)));
            end;

         when N_Op_Add | N_Op_Multiply | N_Op_Subtract =>
            --  The arguments of arithmetic functions have to be of base
            --  scalar types
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
            begin
               Current_Type := Base_Why_Type (Left, Right);
               T :=
                 New_Binary_Op
                   (Ada_Node => Expr,
                    Left     => Transform_Expr (Left,
                                                Current_Type,
                                                Domain,
                                                Local_Params),
                    Right    => Transform_Expr (Right,
                                                Current_Type,
                                                Domain,
                                                Local_Params),
                    Op       => Transform_Binop (Nkind (Expr)),
                    Op_Type  => Get_Base_Type (Current_Type));
               T := Apply_Modulus (Etype (Expr), T, Domain);
            end;

         when N_Op_Divide =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Name  : W_Identifier_Id;
               L_Why, R_Why : W_Expr_Id;
            begin
               Current_Type := Base_Why_Type (Left, Right);
               L_Why :=
                 Transform_Expr (Left,
                                 Current_Type,
                                 Domain,
                                 Local_Params);
               R_Why :=
                 Transform_Expr (Right,
                                 Current_Type,
                                 Domain,
                                 Local_Params);
               Name := New_Division (Get_Base_Type (Current_Type));
               if Domain = EW_Prog and then Do_Division_Check (Expr) then
                  T :=
                    New_VC_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => To_Program_Space (Name),
                       Progs    => (1 => L_Why, 2 => R_Why),
                       Reason   => VC_Division_Check);
               else
                  T :=
                    New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Name,
                       Args    => (1 => L_Why, 2 => R_Why));
               end if;

               T := Apply_Modulus (Etype (Expr), T, Domain);
            end;

         when N_Op_Rem | N_Op_Mod =>
            declare
               Left  : constant Node_Id := Left_Opnd (Expr);
               Right : constant Node_Id := Right_Opnd (Expr);
               Name  : W_Identifier_Id;
            begin
               Current_Type := Base_Why_Type (Left, Right);
               Name := (if Nkind (Expr) = N_Op_Rem then
                          To_Ident (WNE_Integer_Rem)
                        else
                          To_Ident (WNE_Integer_Mod));
               Name := (if Domain = EW_Prog then
                          To_Program_Space (Name)
                        else
                          Name);
               T :=
                 New_VC_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => Name,
                    Progs    =>
                      (1 => Transform_Expr (Left,
                                            Current_Type,
                                            Domain,
                                            Local_Params),
                       2 => Transform_Expr (Right,
                                            Current_Type,
                                            Domain,
                                            Local_Params)),
                    Reason   => VC_Division_Check);
            end;

         when N_Op_Expon =>
            declare
               Left    : constant Node_Id := Left_Opnd (Expr);
               Right   : constant Node_Id := Right_Opnd (Expr);
               Name    : W_Identifier_Id;
               W_Right : constant W_Expr_Id :=
                 Transform_Expr (Right,
                                 EW_Int_Type,
                                 Domain,
                                 Local_Params);
            begin
               Current_Type := Base_Why_Type (Left);
               Name := New_Exp (Get_Base_Type (Current_Type));

               T := New_Call
                      (Ada_Node => Expr,
                       Domain   => Domain,
                       Name     => Name,
                       Args     =>
                         (1 => Transform_Expr (Left,
                                               Current_Type,
                                               Domain,
                                               Local_Params),
                          2 => W_Right));

            end;

         when N_Op_Not =>
            Current_Type := EW_Bool_Type;
            if Domain = EW_Term then
               T :=
                 New_Call
                   (Ada_Node => Expr,
                    Domain   => Domain,
                    Name     => New_Identifier (Name => "notb"),
                    Args     =>
                      (1 => Transform_Expr (Right_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Local_Params)));
            else
               T :=
                 New_Not
                   (Right  => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                    Domain => Domain);
            end if;

         when N_Op_And =>
            T :=
               New_And_Expr
                 (Left   => Transform_Expr (Left_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Local_Params),
                  Right  => Transform_Expr (Right_Opnd (Expr),
                                            EW_Bool_Type,
                                            Domain,
                                            Local_Params),
                  Domain => Domain);
            Current_Type := EW_Bool_Type;

         when N_Op_Or =>
            T :=
               New_Or_Expr
                 (Left     => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                  Right    => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                  Domain   => Domain);
            Current_Type := EW_Bool_Type;

         when N_Op_Xor =>
            T :=
               New_Xor_Expr
                 (Left     => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                  Right    => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                  Domain   => Domain);
            Current_Type := EW_Bool_Type;

         when N_Short_Circuit =>
            Short_Circuit : declare

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id;
               --  Dispatch over functions to create a short-circuit Why expr

               ----------------------------
               -- New_Short_Circuit_Expr --
               ----------------------------

               function New_Short_Circuit_Expr
                 (Left, Right : W_Expr_Id;
                  Domain      : EW_Domain) return W_Expr_Id
               is
               begin
                  if Nkind (Expr) = N_And_Then then
                     return New_And_Then_Expr (Left, Right, Domain);
                  else
                     return New_Or_Else_Expr (Left, Right, Domain);
                  end if;
               end New_Short_Circuit_Expr;

            --  Start of Short_Circuit

            begin
               if Present (Actions (Expr)) then
                  Transform_Actions_Preparation (Actions (Expr), Local_Params);
               end if;

               T :=
                 New_Short_Circuit_Expr
                   (Left   => Transform_Expr (Left_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                    Right  => Transform_Expr (Right_Opnd (Expr),
                                              EW_Bool_Type,
                                              Domain,
                                              Local_Params),
                    Domain => Domain);

               if Present (Actions (Expr)) then
                  T := Transform_Actions (Actions (Expr),
                                          T,
                                          Domain,
                                          Local_Params);
               end if;

               Current_Type := EW_Bool_Type;
            end Short_Circuit;

         when N_In =>
            T := Transform_Membership_Expression (Local_Params, Domain, Expr);

         when N_Quantified_Expression =>
            T := Transform_Quantified_Expression (Expr, Domain, Local_Params);
            Current_Type := EW_Bool_Type;

         when N_If_Expression =>
            declare
               Cond        : constant Node_Id := First (Expressions (Expr));
               Then_Part   : constant Node_Id := Next (Cond);
               Else_Part   : constant Node_Id := Next (Then_Part);
               Cond_Domain : constant EW_Domain :=
                 (if Domain = EW_Term then EW_Pred else Domain);
               Then_Expr, Else_Expr : W_Expr_Id;
               Condition   : W_Expr_Id;
            begin
               Then_Expr :=
                 Transform_Expr_With_Actions (Then_Part,
                                              Then_Actions (Expr),
                                              Current_Type,
                                              Domain,
                                              Local_Params);
               Else_Expr :=
                 Transform_Expr_With_Actions (Else_Part,
                                              Else_Actions (Expr),
                                              Current_Type,
                                              Domain,
                                              Local_Params);
               Local_Params.Gen_Image := False;
               Condition :=
                 +Transform_Expr (Cond,
                                  EW_Bool_Type,
                                  Cond_Domain,
                                  Local_Params);

               T :=
                  New_Conditional
                     (Ada_Node  => Expr,
                      Domain    => Domain,
                      Condition => Condition,
                      Then_Part => Then_Expr,
                      Else_Part => Else_Expr);
            end;

         when N_Type_Conversion =>
            T := Transform_Expr (Expression (Expr),
                                 Expected_Type,
                                 Domain,
                                 Local_Params);
            Current_Type := Expected_Type;

         when N_Unchecked_Type_Conversion =>
            --  Compiler inserted conversions are trusted
            pragma Assert (not Comes_From_Source (Expr));
            return Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   Domain,
                                   Local_Params);

         when N_Function_Call =>
            declare
               Subp       : constant Entity_Id := Entity (Name (Expr));
               --  Retrieve type of function result from function called
               Name       : constant W_Identifier_Id :=
                 To_Why_Id (Subp, Domain, Local => False);
               Nb_Of_Refs : Natural;
               Args       : constant W_Expr_Array :=
                 Compute_Call_Args (Expr, Domain, Nb_Of_Refs, Local_Params);
            begin
               Current_Type := Type_Of_Node (Etype (Subp));
               if Why_Subp_Has_Precondition (Subp) then
                  T :=
                    +New_VC_Call
                    (Name     => Name,
                     Progs    => Args,
                     Ada_Node => Expr,
                     Domain   => Domain,
                     Reason   => VC_Precondition);
               else
                  T :=
                    New_Call
                      (Name     => Name,
                       Args     => Args,
                       Ada_Node => Expr,
                       Domain   => Domain);
               end if;
               pragma Assert (Nb_Of_Refs = 0,
                              "Only pure functions are in alfa");
            end;

         when N_Indexed_Component | N_Selected_Component =>
            T := One_Level_Access (Expr,
                                   Transform_Expr
                                     (Prefix (Expr), Domain, Local_Params),
                                   Domain,
                                   Local_Params,
                                   Current_Type);

         when N_Attribute_Reference =>
            T := Transform_Attr (Expr,
                                 Domain,
                                 Current_Type,
                                 Local_Params);

         when N_Case_Expression =>
            T := Case_Expr_Of_Ada_Node
                   (Expr,
                    Expected_Type,
                    Domain,
                    Local_Params);
            Current_Type := Expected_Type;

         when N_Expression_With_Actions =>
            if not (Domain = EW_Prog) then
               Ada.Text_IO.Put_Line
                 ("[Transform_Expr] expression with action");
               raise Not_Implemented;
            end if;

            T :=
               +Sequence
                 (Transform_Statements_And_Declarations (Actions (Expr)),
                  +Transform_Expr (Expression (Expr),
                                   Expected_Type,
                                   EW_Prog,
                                   Local_Params));

         when N_Qualified_Expression =>
            Current_Type := Base_Why_Type (Expression (Expr));
            T := Transform_Expr (Expression (Expr),
                                 Current_Type,
                                 Domain,
                                 Local_Params);

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Expr] kind ="
                                  & Node_Kind'Image (Nkind (Expr)));
            raise Not_Implemented;
         end case;
      end if;

      --  We now have the translation of the Ada expression in [T], pending
      --  checks and conversion. We now do the wrapping up to insert all those
      --  if needed.

      --  This label will be used for pretty printing the expression

      if Pretty_Label /= Why_Empty then
         T :=
           New_Label (Labels =>
                        (1 => Pretty_Label,
                         2 => New_Located_Label (Expr, Is_VC => False)),
                      Def => T,
                      Domain => Domain);
      end if;

      --  Insert an overflow check if flag Do_Overflow_Check is set. No
      --  conversion should be needed, as overflow checks are only set on
      --  intermediate expressions, whose transformation into Why should
      --  always have type "int" or "real". We start by checking that Expr has
      --  a kind on which we can call Do_Overflow_Check, otherwise there is
      --  nothing to do.

      --  Note that N_Type_Conversions *may* have a Do_Overflow_Check flag, but
      --  they are actually for range checks and are checked elsewhere. See the
      --  documentation of sinfo.ads.

      if Domain = EW_Prog
        and then Nkind (Expr) in N_Attribute_Reference |
                                 N_Case_Expression     |
                                 N_If_Expression       |
                                 N_Op
        and then Do_Overflow_Check (Expr)
      then
         declare

            --  The multiplication and division operations on fixed-point
            --  types have a return type of universal_fixed (with no bounds),
            --  which is used as an overload resolution trick to allow
            --  free conversion between certain real types on the result of
            --  multiplication or division. The target non-universal type
            --  determines the actual sort of multiplication or division
            --  performed, and therefore determines the possibility of
            --  overflow. In the compiler, the multiplication is expanded so
            --  the operands are first converted to some common type, so back
            --  ends don't see the universal_fixed Etype. Here, we are seeing
            --  the unexpanded operation because we are running in a mode that
            --  disables the expansion. Hence, we recognize the universal_fixed
            --  case specially and in that case use the target type of the
            --  enclosing conversion.

            Typ : constant Entity_Id :=
              (if Nkind_In (Expr, N_Op_Multiply, N_Op_Divide)
                 and then Etype (Expr) = Universal_Fixed
                 and then Nkind (Parent (Expr)) = N_Type_Conversion
               then
                 Etype (Parent (Expr))
               else
                 Etype (Expr));

            --  Depending on the current mode for overflow checks, the
            --  operation is either done in the base type (Strict mode), or in
            --  Long_Long_Integer (Minimized mode) if needed, or in arbitrary
            --  precision if needed (Eliminated mode). A check may only be
            --  generated in the Strict and Minimized modes, and the type used
            --  for the bounds is the base type in the first case, and
            --  Long_Long_Integer in the second case (which is its own base
            --  type).

            Mode : Overflow_Mode_Type;

         begin
            case Params.Phase is
               when Generate_VCs_For_Body =>
                  Mode := Opt.Suppress_Options.Overflow_Mode_General;
               when Generate_VCs_For_Assertion =>
                  Mode := Opt.Suppress_Options.Overflow_Mode_Assertions;
               when others =>
                  raise Program_Error;
            end case;

            case Mode is
               when Strict =>
                  T := Insert_Overflow_Check (Expr, T, Typ);
               when Minimized =>
                  T := Insert_Overflow_Check
                    (Expr, T, Standard_Integer_64);
               when Eliminated =>
                  null;
               when Not_Set =>
                  raise Program_Error;
            end case;
         end;
      end if;

      --  Convert the expression to the expected type, if needed. This is
      --  intertwined with inserting range checks, and Insert_Conversion does
      --  both. This is because range checks need to be done on the Why "int"
      --  type, so they may trigger a conversion, or if a conversion is already
      --  needed, must be done on the "right side" of the conversion.
      --  Note that Insert_Conversion is smart enough to not insert any
      --  conversion when it's not needed.

      --  A range check is needed only in programs (Domain EW_Prog), and on
      --  nodes that have the range check flag. For type conversions, the
      --  Do_Overflow_Check actually means that a range check is needed,
      --  instead of an overflow check (see sinfo.ads and the discussion of
      --  range checks and overflow checks there). Because range checks are
      --  determined by looking at the parent node, in that special case we go
      --  one step down for the Range_Check_Node.

      if Domain in EW_Term | EW_Prog then
         declare
            Range_Check_Node : Node_Id := Empty;
            Discr_Check_Node : Node_Id := Empty;
         begin

            --  ??? Protect array types, range checks currently broken for
            --  those

            if Domain /= EW_Prog then
               Range_Check_Node := Empty;
            elsif Do_Range_Check (Expr) then
               Range_Check_Node := Expr;
            elsif Nkind (Expr) = N_Type_Conversion and then
              Do_Overflow_Check (Expr) then
               Range_Check_Node := Expression (Expr);
            end if;

            if Nkind (Parent (Expr)) in
              N_Type_Conversion | N_Assignment_Statement | N_Op_And |
                N_Op_Or | N_Op_Xor and then
              Do_Length_Check (Parent (Expr)) and then
              Domain = EW_Prog then
               Range_Check_Node := Expr;
            end if;

            if Domain = EW_Prog and then
              Nkind (Parent (Expr)) in
              N_Type_Conversion | N_Assignment_Statement then

               --  ??? in which cases exactly do we need a check?

               Discr_Check_Node := Parent (Expr);
            end if;

            T := Insert_Conversion (Domain        => Domain,
                                    Ada_Node      => Expr,
                                    Expr          => T,
                                    From          => Current_Type,
                                    To            => Expected_Type,
                                    Range_Check   => Range_Check_Node,
                                    Discr_Check   => Discr_Check_Node);
         end;
      end if;

      return T;
   end Transform_Expr;

   function Transform_Expr
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id is
   begin
      return Transform_Expr (Expr,
                             Type_Of_Node (Expr),
                             Domain,
                             Params);
   end Transform_Expr;

   ---------------------------------
   -- Transform_Expr_With_Actions --
   ---------------------------------

   function Transform_Expr_With_Actions
     (Expr          : Node_Id;
      Actions       : List_Id;
      Expected_Type : W_Base_Type_Id;
      Domain        : EW_Domain;
      Params        : Transformation_Params) return W_Expr_Id
   is
      Local_Params : Transformation_Params := Params;
      T            : W_Expr_Id;

   begin
      if Present (Actions) then
         Transform_Actions_Preparation (Actions, Local_Params);
      end if;

      T := Transform_Expr (Expr,
                           Expected_Type,
                           Domain,
                           Local_Params);

      if Present (Actions) then
         T := Transform_Actions (Actions,
                                 T,
                                 Domain,
                                 Local_Params);
      end if;

      return T;
   end Transform_Expr_With_Actions;

   function Transform_Expr_With_Actions
     (Expr    : Node_Id;
      Actions : List_Id;
      Domain  : EW_Domain;
      Params  : Transformation_Params) return W_Expr_Id is
   begin
      return Transform_Expr_With_Actions (Expr,
                                          Actions,
                                          Type_Of_Node (Expr),
                                          Domain,
                                          Params);
   end Transform_Expr_With_Actions;

   --------------------------
   -- Transform_Identifier --
   --------------------------

   function Transform_Identifier (Params       : Transformation_Params;
                                  Expr         : Node_Id;
                                  Ent          : Entity_Id;
                                  Domain       : EW_Domain;
                                  Current_Type : out W_Base_Type_Id)
                                  return W_Expr_Id
   is
      C   : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Params.Name_Map, Ent);
      T   : W_Expr_Id;
   begin

      --  The special cases of this function are:
      --  * parameters, whose names are stored in Params.Name_Map (these can
      --    also be refs)
      --  * enumeration literals (we have a separate function)
      --  * ids of Standard.ASCII (transform to integer)
      --  * loop parameters (set type to integer)
      --  * quantified variables (use local name instead of global name)

      Current_Type := Type_Of_Node (Expr);

      if Ada_Ent_To_Why.Has_Element (C) then
         T := +Ada_Ent_To_Why.Element (C);
      elsif Ekind (Ent) = E_Enumeration_Literal then
         T := Transform_Enum_Literal (Expr, Ent, Current_Type, Domain);
      elsif Sloc (Ent) = Standard_ASCII_Location then
         T :=
           New_Integer_Constant
             (Value => Char_Literal_Value (Constant_Value (Ent)));
         Current_Type := EW_Int_Type;
      elsif Ekind (Ent) = E_Loop_Parameter and then
        Is_Quantified_Loop_Param (Ent) then
         T := +New_Identifier (Name => Full_Name (Ent));
      else
         T := +To_Why_Id (Ent, Domain);
      end if;
      if Ekind (Ent) = E_Loop_Parameter and then
        not Type_In_Formal_Container (Etype (Ent)) then
         Current_Type := EW_Int_Type;
      end if;
      if Is_Mutable_In_Why (Ent) and then Params.Ref_Allowed then
         T := New_Deref (Ada_Node => Expr, Right => +T);
      end if;
      return T;
   end Transform_Identifier;

   -------------------------------------
   -- Transform_Membership_Expression --
   -------------------------------------

   function Transform_Membership_Expression
     (Params : Transformation_Params;
      Domain : EW_Domain;
      Expr   : Node_Id)
     return W_Expr_Id
   is
      function Transform_Alternative (Var, Alt : Node_Id) return W_Expr_Id;
      --  If the alternative Alt is a subtype mark, transform it as a simple
      --  membership test "Var in Alt". Otherwise transform it as an equality
      --  test "Var = Alt".

      function Transform_Simple_Membership_Expression
        (Var, In_Expr : Node_Id) return W_Expr_Id;
      --  Transform a simple membership test "Var in In_Expr"

      ---------------------------
      -- Transform_Alternative --
      ---------------------------

      function Transform_Alternative (Var, Alt : Node_Id) return W_Expr_Id is
         Result : W_Expr_Id;
      begin
         if (Is_Entity_Name (Alt) and then Is_Type (Entity (Alt)))
           or else Nkind (Alt) = N_Range
         then
            Result := Transform_Simple_Membership_Expression (Var, Alt);
         else
            declare
               BT : constant W_Base_Type_Id := Base_Why_Type (Var, Alt);
            begin
               Result := New_Comparison
                 (Cmp       => EW_Eq,
                  Left      => Transform_Expr (Var, Domain, Params),
                  Right     => Transform_Expr (Alt, Domain, Params),
                  Arg_Types => BT,
                  Domain    => Domain);
            end;
         end if;

         return Result;
      end Transform_Alternative;

      --------------------------------------------
      -- Transform_Simple_Membership_Expression --
      --------------------------------------------

      function Transform_Simple_Membership_Expression
        (Var, In_Expr : Node_Id) return W_Expr_Id
      is
         Subdomain  : constant EW_Domain :=
           (if Domain = EW_Pred then EW_Term else Domain);
         Bool_True  : constant W_Expr_Id :=
           New_Literal (Domain => EW_Term,
                        Value  => EW_True);
         Check_Expr : constant W_Expr_Id :=
           Transform_Expr (Var,
                           Base_Why_Type (Var),
                           Subdomain,
                           Params);
      begin

         --  First handle the case where there is a subtype mark of a record
         --  type on the right.

         if Nkind (In_Expr) in N_Identifier | N_Expanded_Name
           and then Ekind (Entity (In_Expr)) in Type_Kind
           and then Ekind (Unique_Entity (Entity (In_Expr))) in Record_Kind
         then
            declare
               Ty   : constant Entity_Id :=
                 Unique_Entity (Entity (In_Expr));
            begin

               --  eliminate trivial cases first, the membership test is always
               --  true here.

               if Root_Type (Ty) = Ty or else
                 not Has_Discriminants (Ty) or else
                 not Is_Constrained (Ty)
               then
                  return Bool_True;
               end if;

               declare
                  Call : constant W_Expr_Id :=
                    New_Call (Domain => Domain,
                              Name =>
                                Prefix (S        => Full_Name (Ty),
                                        W        => WNE_Range_Pred,
                                        Ada_Node => Ty),
                              Args =>
                                Prepare_Args_For_Subtype_Check
                                  (Ty, Check_Expr));
               begin
                  return
                    New_Conditional
                      (Domain    => Domain,
                       Condition => Call,
                       Then_Part => Bool_True,
                         Else_Part =>
                           New_Literal (Domain => EW_Term,
                                        Value => EW_False));
               end;
            end;
         else
            return Range_Expr (In_Expr,
                               Check_Expr,
                               Domain,
                               Params);
         end if;
      end Transform_Simple_Membership_Expression;

      Var     : constant Node_Id := Left_Opnd (Expr);
      Result  : W_Expr_Id;

   --  Start of processing for Transform_Membership_Expression

   begin
      if Present (Alternatives (Expr)) then
         declare
            Alt : Node_Id;
         begin
            Alt := Last (Alternatives (Expr));
            Result := Transform_Alternative (Var, Alt);

            Prev (Alt);
            while Present (Alt) loop
               Result :=
                 New_Or_Else_Expr (Left   => Transform_Alternative (Var, Alt),
                                   Right  => Result,
                                   Domain => Domain);
               Prev (Alt);
            end loop;
         end;

      else
         Result :=
           Transform_Simple_Membership_Expression (Var, Right_Opnd (Expr));
      end if;

      return Result;
   end Transform_Membership_Expression;

   ----------------------------
   -- Transform_Pragma_Check --
   ----------------------------

   procedure Transform_Pragma_Check
     (Stmt    : Node_Id;
      Runtime : out W_Prog_Id;
      Pred    : out W_Pred_Id)
   is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (Stmt));
      Arg2 : constant Node_Id := Next (Arg1);
      Expr : constant Node_Id := Expression (Arg2);
      Params : Transformation_Params := Assert_Params;
   begin

      --  Pragma Check generated for Pre/Postconditions are
      --  ignored.

      if Chars (Get_Pragma_Arg (Arg1)) = Name_Precondition
           or else
         Chars (Get_Pragma_Arg (Arg1)) = Name_Postcondition
      then
         Runtime := New_Void (Stmt);
         Pred := True_Pred;
         return;
      end if;

      if Present (Expr) then
         Runtime := New_Ignore
           (Prog => +Transform_Expr (Expr, EW_Prog, Params => Params));
         Params.Gen_Image := True;
         Pred := +Transform_Expr (Expr, EW_Pred, Params => Params);
         return;
      else
         raise Program_Error;
      end if;
   end Transform_Pragma_Check;

   -------------------------------------
   -- Transform_Quantified_Expression --
   -------------------------------------

   function Transform_Quantified_Expression
     (Expr   : Node_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      -----------------------
      -- Local Subprograms --
      -----------------------

      function Extract_Index_Entity
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id;
      --  Return the entity used for indexing in the quantification

      function Extract_Set_Node
        (N          : Node_Id;
         Over_Range : Boolean) return Node_Id;
      --  Return the set over which the quantification is performed

      --------------------------
      -- Extract_Index_Entity --
      --------------------------

      function Extract_Index_Entity
        (N          : Node_Id;
         Over_Range : Boolean) return Entity_Id
      is
      begin
         if Over_Range then
            return Defining_Identifier (Loop_Parameter_Specification (N));
         else
            return Defining_Identifier (Iterator_Specification (N));
         end if;
      end Extract_Index_Entity;

      ----------------------
      -- Extract_Set_Node --
      ----------------------

      function Extract_Set_Node
        (N          : Node_Id;
         Over_Range : Boolean) return Node_Id
      is
      begin
         if Over_Range then
            return
              Discrete_Subtype_Definition (Loop_Parameter_Specification (N));
         else
            return Get_Container_In_Iterator_Specification
              (Iterator_Specification (N));
         end if;
      end Extract_Set_Node;

      Over_Range : constant Boolean :=
                     Present (Loop_Parameter_Specification (Expr));
      --  The quantification is either over a scalar range, in which case
      --  there is a loop-parameter-specification component, otherwise
      --  the quantification is over a container and there is an
      --  iterator-specification component.

      Index_Ent  : constant Entity_Id :=
                     Extract_Index_Entity (Expr, Over_Range);
      Range_E    : constant Node_Id   := Extract_Set_Node (Expr, Over_Range);
      Index_Type : constant Entity_Id := Etype (Index_Ent);
      Why_Id     : constant W_Identifier_Id :=
                     New_Identifier (Name     => Full_Name (Index_Ent));
      Index_Base : constant W_Primitive_Type_Id :=
                     (if Over_Range then
                        New_Base_Type (Base_Type => EW_Int)
                      else
                        Why_Logic_Type_Of_Ada_Type (Index_Type));

   --  Start of Transform_Quantified_Expression

   begin
      --  Simplest case, the quantification in Ada is translated as a
      --  quantification in Why3.

      if Domain = EW_Pred then
         declare
            Conclusion : constant W_Pred_Id :=
                           +Transform_Expr (Condition (Expr),
                                            EW_Pred, Params);
            Constraint : constant W_Pred_Id :=
              (if Over_Range then
                 +Range_Expr (Range_E, +Why_Id, EW_Pred, Params)
               else
                 +Has_Element_Expr (Range_E, +Why_Id, EW_Pred, Params));
            Connector  : constant EW_Connector :=
              (if All_Present (Expr) then EW_Imply else EW_And);
            Quant_Body : constant W_Pred_Id :=
              New_Connection
                (Op     => Connector,
                 Left   => +Constraint,
                 Right  => +Conclusion);
         begin
            if All_Present (Expr) then
               return
                  New_Universal_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Why_Id),
                      Var_Type  => Index_Base,
                      Pred      => Quant_Body);
            else
               return
                  New_Existential_Quantif
                     (Ada_Node  => Expr,
                      Variables => (1 => Why_Id),
                      Var_Type  => Index_Base,
                      Pred      => Quant_Body);
            end if;
         end;

      --  We are interested in the checks for the entire range, and
      --  in the return value of the entire expression, but we are
      --  not interested in the exact order in which things are
      --  evaluated. We also do not want to translate the expression
      --  function by a loop. So our scheme is the following:
      --    for all I in Cond => Expr
      --
      --  becomes:
      --    (let i = ref [ int ] in
      --       if cond then ignore (expr));
      --    [ { } bool { result = true <-> expr } ]
      --  The condition is a formula that expresses that i is in the
      --  range given by the quantification.

      elsif Domain = EW_Prog then
         declare
            Why_Expr   : constant W_Prog_Id :=
                           New_Ignore
                             (Prog =>
                                +Transform_Expr (Condition (Expr),
                                                 EW_Prog, Params));
            Range_Cond : W_Prog_Id;
         begin
            Range_Cond :=
              (if Over_Range then
                 +Range_Expr (Range_E, +Why_Id, EW_Prog, Params)
               else
                 +Has_Element_Expr (Range_E, +Why_Id, EW_Prog, Params));
            return
              +Sequence
                (New_Binding
                   (Name    => Why_Id,
                    Def     =>
                      +New_Simpl_Any_Prog (Index_Base),
                    Context =>
                      New_Conditional
                        (Domain    => EW_Prog,
                         Condition => +Range_Cond,
                         Then_Part => +Why_Expr)),
                 New_Assume_Statement
                   (Ada_Node    => Expr,
                    Return_Type => New_Base_Type (Base_Type => EW_Bool),
                    Post        =>
                      +W_Expr_Id'(New_Connection
                        (Domain   => EW_Pred,
                         Left     =>
                           New_Relation
                             (Domain   => EW_Pred,
                              Op_Type  => EW_Bool,
                              Left     => +To_Ident (WNE_Result),
                              Op       => EW_Eq,
                              Right    => +True_Term),
                         Op       => EW_Equivalent,
                         Right    =>
                           +Transform_Expr (Expr, EW_Pred, Params)))));
         end;

      --  It is trivial to promote a predicate to a term, by doing
      --    if pred then True else False

      else
         declare
            Pred : constant W_Expr_Id :=
                     Transform_Quantified_Expression
                       (Expr, EW_Pred, Params);
         begin
            return
              New_Conditional (Domain    => EW_Term,
                               Condition => Pred,
                               Then_Part =>
                                 New_Literal (Value => EW_True,
                                              Domain => Domain,
                                              Ada_Node => Standard_Boolean),
                               Else_Part =>
                                 New_Literal (Value => EW_False,
                                              Domain => Domain,
                                              Ada_Node => Standard_Boolean));
         end;
      end if;
   end Transform_Quantified_Expression;

   ---------------------------------------------
   -- Transform_Record_Component_Associations --
   ---------------------------------------------

   function Transform_Record_Component_Associations
     (Domain      : EW_Domain;
      Typ         : Entity_Id;
      Assocs      : List_Id;
      Params      : Transformation_Params) return W_Field_Association_Array
   is
      Component   : Entity_Id := First_Component_Or_Discriminant (Typ);
      Association : Node_Id := Nlists.First (Assocs);
      Result      : W_Field_Association_Array (1 .. Number_Components (Typ));
      J           : Positive := Result'First;

   --  Start of Transform_Record_Component_Associations

   begin
      while Component /= Empty loop
         declare
            Expr : W_Expr_Id;
         begin
            if Present (Association)
              and then Matching_Component_Association (Component, Association)
            then
               if not Box_Present (Association) then
                  Expr := Transform_Expr
                    (Expression (Association),
                     +Why_Logic_Type_Of_Ada_Type (Etype (Component)),
                     Domain, Params);
               else
                  pragma Assert (Domain = EW_Prog);
                  Expr :=
                     +New_Simpl_Any_Prog
                         (T =>
                            +Why_Logic_Type_Of_Ada_Type (Etype (Component)));
               end if;
               Next (Association);
            else
               pragma Assert (Domain = EW_Prog);
               Expr :=
                 +New_Simpl_Any_Prog
                   (T =>
                      +Why_Logic_Type_Of_Ada_Type (Etype (Component)));
            end if;
            Result (J) :=
               New_Field_Association
                  (Domain => Domain,
                   Field  => To_Why_Id (Component),
                   Value  => Expr);
            J := J + 1;
            Component := Next_Component_Or_Discriminant (Component);
         end;
      end loop;
      pragma Assert (No (Association));
      return Result;
   end Transform_Record_Component_Associations;

   ----------------------------------------
   -- Transform_Statement_Or_Declaration --
   ----------------------------------------

   function Transform_Statement_Or_Declaration
     (Stmt_Or_Decl           : Node_Id;
      Assert_And_Cut : out W_Pred_Id) return W_Prog_Id is
   begin
      --  Make sure that Assert_And_Cut is initialized

      Assert_And_Cut := Why_Empty;

      case Nkind (Stmt_Or_Decl) is
         when N_Label | N_Null_Statement =>
            return New_Void (Stmt_Or_Decl);

         when N_Assignment_Statement =>

            return Transform_Assignment_Statement (Stmt_Or_Decl);

         --  Translate a return statement by raising the predefined exception
         --  for returns, which is caught at the end of the subprogram. For
         --  functions, store the value returned in the local special variable
         --  for returned values, prior to raising the exception.

         when N_Simple_Return_Statement =>
            declare
               Raise_Stmt  : constant W_Prog_Id :=
                               New_Raise
                                 (Ada_Node => Stmt_Or_Decl,
                                  Name     => To_Ident (WNE_Result_Exc));
               Result_Stmt : W_Prog_Id;
            begin
               if Expression (Stmt_Or_Decl) /= Empty then
                  declare
                     Return_Type : constant W_Base_Type_Id :=
                       Type_Of_Node (Etype (Return_Applies_To
                         (Return_Statement_Entity (Stmt_Or_Decl))));
                  begin
                     Result_Stmt :=
                       New_Assignment
                         (Ada_Node => Stmt_Or_Decl,
                          Name     => Name_For_Result,
                          Value    =>
                            +Transform_Expr (Expression (Stmt_Or_Decl),
                                             Return_Type,
                                             EW_Prog,
                                             Params => Body_Params));
                     return Sequence (Result_Stmt, Raise_Stmt);
                  end;
               else
                  return Raise_Stmt;
               end if;
            end;

         when N_Procedure_Call_Statement =>
            declare
               Nb_Of_Refs : Natural;
               Args       : constant W_Expr_Array :=
                 Compute_Call_Args
                   (Stmt_Or_Decl, EW_Prog, Nb_Of_Refs, Params => Body_Params);
               Subp       : constant Entity_Id := Entity (Name (Stmt_Or_Decl));
               Why_Name   : constant W_Identifier_Id :=
                 To_Why_Id (Subp, EW_Prog);
               Call       : constant W_Expr_Id :=
                 (if Why_Subp_Has_Precondition (Subp) then
                   +New_VC_Call
                     (Stmt_Or_Decl, Why_Name, Args, VC_Precondition, EW_Prog)
                  else
                    New_Call (Stmt_Or_Decl, EW_Prog, Why_Name, Args));
            begin
               if Nb_Of_Refs = 0 then
                  return +Call;
               else
                  return Insert_Ref_Context
                           (Body_Params, Stmt_Or_Decl, +Call, Nb_Of_Refs);
               end if;
            end;

         when N_If_Statement =>
            declare
               Tail : W_Prog_Id := Transform_Statements_And_Declarations
                                     (Else_Statements (Stmt_Or_Decl));
            begin
               if Present (Elsif_Parts (Stmt_Or_Decl)) then
                  declare
                     Cur : Node_Id := Last (Elsif_Parts (Stmt_Or_Decl));
                  begin

                     --  Beginning from the tail that consists of the
                     --  translation of the Else part, possibly a no-op,
                     --  translate the list of elsif parts into a chain of
                     --  if-then-else Why expressions.

                     while Present (Cur) loop
                        Tail :=
                          New_Label
                            (Labels => (1 =>
                                         New_Located_Label
                                           (Cur, Is_VC => False)),
                             Def    =>
                             +New_Simpl_Conditional
                               (Condition =>
                                  Transform_Expr_With_Actions
                                    (Condition (Cur),
                                     Condition_Actions (Cur),
                                     EW_Bool_Type,
                                     EW_Prog,
                                     Params => Body_Params),
                                Then_Part =>
                                  +Transform_Statements_And_Declarations
                                    (Then_Statements (Cur)),
                                Else_Part => +Tail,
                                Domain    => EW_Prog));
                        Prev (Cur);
                     end loop;
                  end;
               end if;

               --  Finish by putting the main if-then-else on top.

               return
                 +New_Simpl_Conditional
                 (Condition => Transform_Expr (Condition (Stmt_Or_Decl),
                                               EW_Bool_Type,
                                               EW_Prog,
                                               Params => Body_Params),
                    Then_Part =>
                      +Transform_Statements_And_Declarations
                        (Then_Statements (Stmt_Or_Decl)),
                    Else_Part => +Tail,
                    Domain    => EW_Prog);
            end;

         when N_Raise_xxx_Error =>
            Ada.Text_IO.Put_Line ("[Transform_Statement] raise xxx error");
            raise Not_Implemented;

         when N_Object_Declaration    |
              N_Subtype_Declaration   |
              N_Full_Type_Declaration =>
            return Transform_Declaration (Stmt_Or_Decl);

         when N_Loop_Statement =>
            return Transform_Loop_Statement (Stmt_Or_Decl);

         when N_Exit_Statement =>
            return Transform_Exit_Statement (Stmt_Or_Decl);

         when N_Case_Statement =>
            return
              +Case_Expr_Of_Ada_Node
                 (N           => Stmt_Or_Decl,
                  Domain      => EW_Prog,
                  Params      => Body_Params);

         when N_Block_Statement =>
            return Transform_Block_Statement (Stmt_Or_Decl);

         when N_Pragma =>
            case Get_Pragma_Id (Pragma_Name (Stmt_Or_Decl)) is
               when Pragma_Annotate =>
                  return New_Void (Stmt_Or_Decl);

               when Pragma_Check =>
                  declare
                     Check_Expr : W_Prog_Id;
                     Pred       : W_Pred_Id;

                     --  Mark non-selected loop invariants (those not occurring
                     --  next to the first batch of selected variants and
                     --  invariants) as loop invariant VCs.

                     Reason : constant VC_Kind :=
                       (if Is_Pragma_Check (Stmt_Or_Decl, Name_Loop_Invariant)
                        then
                          VC_Loop_Invariant
                        else
                          VC_Assert);

                  begin
                     Transform_Pragma_Check (Stmt_Or_Decl, Check_Expr, Pred);

                     if Is_Pragma_Assert_And_Cut (Stmt_Or_Decl) then
                        Assert_And_Cut := Pred;
                        if Check_Expr /= Why_Empty then
                           return Check_Expr;
                        else
                           return New_Void (Stmt_Or_Decl);
                        end if;
                     elsif Is_False_Boolean (+Pred) then
                        return
                          +New_VC_Expr
                            (Ada_Node => Stmt_Or_Decl,
                             Expr     => +New_Identifier (Name => "absurd"),
                             Reason   => Reason,
                             Domain   => EW_Prog);
                     elsif Is_True_Boolean (+Pred) then
                        return New_Void (Stmt_Or_Decl);
                     elsif Check_Expr /= Why_Empty then
                        return
                          Sequence (Check_Expr,
                                    New_Located_Assert
                                      (Stmt_Or_Decl, Pred, Reason));
                     else
                        return New_Located_Assert (Stmt_Or_Decl, Pred, Reason);
                     end if;
                  end;

               when Pragma_Export   |
                    Pragma_Import   |
                    Pragma_Warnings =>
                  return New_Void (Stmt_Or_Decl);

               when others =>
                  Ada.Text_IO.Put_Line
                    ("[Transform_Statement] pragma kind ="
                     & Pragma_Id'Image
                         (Get_Pragma_Id (Pragma_Name (Stmt_Or_Decl))));
                  raise Not_Implemented;
            end case;

         --  ??? Should not occur (L927-029), but until this is fixed, ignore
         --  freeze nodes.

         when N_Freeze_Entity =>
            return New_Void;

         --  Renamings are replaced by the renamed object in the frontend, but
         --  the renaming objects are not removed from the tree. We can safely
         --  ignore them.

         when N_Object_Renaming_Declaration =>
            return New_Void;

         --  Nothing to do for an implicit label declaration

         when N_Implicit_Label_Declaration =>
            return New_Void;

         --  Subprogram declarations are already taken care of explicitly.
         --  They should not be treated as part of a list of declarations.

         when N_Subprogram_Body        |
              N_Subprogram_Declaration =>
            return New_Void;

         when others =>
            Ada.Text_IO.Put_Line ("[Transform_Statement] kind ="
                                  & Node_Kind'Image (Nkind (Stmt_Or_Decl)));
            raise Not_Implemented;
      end case;
   end Transform_Statement_Or_Declaration;

   ------------------------------------------------
   -- Transform_Statement_Or_Declaration_In_List --
   ------------------------------------------------

   function Transform_Statement_Or_Declaration_In_List
     (Stmt_Or_Decl : Node_Id;
      Prev_Prog    : W_Prog_Id) return W_Prog_Id
   is
      Result        : W_Prog_Id := Prev_Prog;
      Cut_Assertion : W_Pred_Id;
      Prog          : constant W_Prog_Id :=
        Transform_Statement_Or_Declaration (Stmt_Or_Decl, Cut_Assertion);
   begin
      Result :=
        Sequence
          (Result,
           New_Label (Labels =>
                        (1 => New_Located_Label
                         (Stmt_Or_Decl,
                            Is_VC => False)),
                      Def    => +Prog));
      if Cut_Assertion /= Why_Empty then
         Result :=
           New_Located_Abstract
             (Ada_Node => Stmt_Or_Decl,
              Expr     => +Result,
              Post     => Cut_Assertion);
      end if;

      return Result;
   end Transform_Statement_Or_Declaration_In_List;

   -------------------------------------------
   -- Transform_Statements_And_Declarations --
   -------------------------------------------

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Of_Nodes.List) return W_Prog_Id
   is
      Result : W_Prog_Id := New_Void;
   begin
      for Cur_Stmt_Or_Decl of Stmts_And_Decls loop
         Result :=
           Transform_Statement_Or_Declaration_In_List
             (Stmt_Or_Decl => Cur_Stmt_Or_Decl,
              Prev_Prog    => Result);
      end loop;
      return Result;
   end Transform_Statements_And_Declarations;

   function Transform_Statements_And_Declarations
     (Stmts_And_Decls : List_Id) return W_Prog_Id
   is
     (Transform_Statements_And_Declarations
        (Get_Statement_And_Declaration_List (Stmts_And_Decls)));

   ------------------------------
   -- Transform_String_Literal --
   ------------------------------

   procedure Transform_String_Literal
     (Params : Transformation_Params;
      N      : Node_Id)
   is
      Name      : constant String := New_Str_Lit_Ident (N);
      Id        : constant W_Identifier_Id :=
        New_Identifier (Ada_Node => N, Name => Name);
      Ty        : constant Entity_Id := Type_Of_Node (N);
      Why_Type  : constant W_Base_Type_Id :=
        New_Base_Type (Base_Type => EW_Abstract, Ada_Node => Ty);
      Decl_File : Why_File := Why_Files (Dispatch_Entity (N));
   begin
      if Params.File = Decl_File.File then
         Decl_File.Cur_Theory := Why_Empty;
      end if;

      Open_Theory (Decl_File, Name,
                   Comment =>
                     "Module for defining a value for string literal "
                       & (if Sloc (N) > 0 then
                            " defined at " & Build_Location_String (Sloc (N))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Emit
        (Decl_File.Cur_Theory,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Id,
            Binders     => (1 .. 0 => <>),
            Return_Type => +Why_Type));
      Close_Theory (Decl_File, Filter_Entity => N);

      if Params.File = Decl_File.File then
         Decl_File.Cur_Theory := Params.Theory;
      end if;

      Strlit_To_Why_Term.Include (Strval (N), +Id);
      Strlit_To_Why_Type.Include (Strval (N), Why_Type);
   end Transform_String_Literal;

   -------------------------------
   -- Why_Subp_Has_Precondition --
   -------------------------------

   function Why_Subp_Has_Precondition (E : Entity_Id) return Boolean is
   begin
      return Has_Precondition (E) or else
        Entity_Is_Instance_Of_Formal_Container (E);
   end Why_Subp_Has_Precondition;

end Gnat2Why.Expr;
