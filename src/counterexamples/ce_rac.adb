------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2021-2023, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;          use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Indefinite_Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Environment_Variables;
with Ada.Numerics.Big_Numbers.Big_Reals;
with Ada.Text_IO;             use Ada.Text_IO;
with CE_Fuzzer;               use CE_Fuzzer;
with CE_Parsing;              use CE_Parsing;
with CE_Utils;                use CE_Utils;
with Common_Containers;       use Common_Containers;
with Elists;                  use Elists;
with Flow_Refinement;         use Flow_Refinement;
with Flow_Types;              use Flow_Types;
with Flow_Utility;            use Flow_Utility;
with GNAT.Traceback;
with GNAT.Traceback.Symbolic;
with GNATCOLL.JSON;           use GNATCOLL.JSON;
with GNATCOLL.Utils;          use GNATCOLL.Utils;
with Gnat2Why_Opts.Reading;
with Gnat2Why.Tables;         use Gnat2Why.Tables;
with Gnat2Why.Util;           use Gnat2Why.Util;
with Namet;                   use Namet;
with Nlists;                  use Nlists;
with Nmake;                   use Nmake;
with Output;                  use Output;
with Sinput;                  use Sinput;
with Snames;                  use Snames;
with SPARK_Atree;             use SPARK_Atree;
with SPARK_Definition;
with SPARK_Util;              use SPARK_Util;
with SPARK_Util.Subprograms;  use SPARK_Util.Subprograms;
with SPARK_Util.Types;        use SPARK_Util.Types;
with Stand;                   use Stand;
with Stringt;
with Treepr;
with Uintp;                   use Uintp;

package body CE_RAC is

   -----------
   -- Types --
   -----------

   procedure Check_Supported_Type (Ty : Entity_Id);
   --  Call RAC_Unsupported if Ty is not supported yet

   ------------
   -- Values --
   ------------

   function No_Value return Opt_Value_Type is
     (Present => False);
   --  Absence of an optional value

   function Some_Value (V : Value_Type) return Opt_Value_Type is
     (Present => True, Content => V);
   --  Presence of an optional value

   function Scalar_Value
     (V  : Scalar_Value_Type;
      Ty : Entity_Id) return Value_Type
   is
     (K                => Scalar_K,
      AST_Ty           => Retysp (Ty),
      Scalar_Content   => new Scalar_Value_Type'(V),
      Initialized_Attr => <>);
   --  Make a value of kind scalar out of a scalar value

   function Enum_Value (E : Entity_Id; Ty : Entity_Id) return Value_Type is
     (Scalar_Value ((K => Enum_K, Enum_Entity => E), Retysp (Ty)));
   --  Make an enum value from an enumeration literal E

   function Enum_Value (I : Uint; Ty : Entity_Id) return Value_Type;
   --  Make an enum value from an enum index I

   function Record_Value
     (F  : Entity_To_Value_Maps.Map;
      Ty : Entity_Id) return Value_Type;
   --  Make a record value with fields F

   function String_Value (Str : String) return Value_Type;
   --  Make an array value for string Str

   function Array_Value
     (First, Last : Big_Integer;
      Values      : Big_Integer_To_Value_Maps.Map;
      Other       : Value_Access;
      Ty          : Entity_Id) return Value_Type
   is
     (K            => Array_K,
      AST_Ty       => Retysp (Ty),
      First_Attr   => (True, First),
      Last_Attr    => (True, Last),
      Array_Values => Values,
      Array_Others => Other);
   --  Make an array value

   function Boolean_Value (B : Boolean; Ty : Entity_Id) return Value_Type;
   --  Make a boolean value, i.e. an enum value

   function Character_Value (C : Character; Ty : Entity_Id) return Value_Type;
   --  Make a character value, i.e. an enum value

   function Value_Boolean (V : Value_Type) return Boolean;
   --  Get the value of a boolean enum value, fail for other types

   function Value_Enum_Integer (V : Value_Type) return Big_Integer;
   --  Shortcut to convert an enum or integer value to an integer (using the
   --  position of the enum literal for enum values).

   function Value_Integer (V : Value_Type) return Big_Integer;
   --  Get the value of an integer value, fail for other types

   function Value_Character (V : Value_Type) return Character;
   --  Get the value of a enumeration value as a character, fail for other
   --  types.

   function To_Integer (I : Uint) return Integer is
     (Integer (UI_To_Int (I)));
   --  Shortcut to convert an Uint to an Integer

   function To_Big_Integer (I : Uint) return Big_Integer is
     (To_Big_Integer (To_Integer (I)));
   --  Shortcut to convert an Uint to a Big_Integer

   function To_Long_Float (B : Big_Integer) return Long_Float;
   --  Convert big integer to Long_Float, raise RAC_Incomplete when out of
   --  range.

   function To_Integer (B : Big_Integer) return Integer;
   --  Convert big integer to integer, raise RAC_Incomplete when out of range

   procedure Check_Integer (I : Big_Integer; Ty : Entity_Id; N : Node_Id);
   --  Check an integer I against the range bounds or apply modulo for type Ty,
   --  signaling errors for node N.

   procedure Check_Integer (V : Value_Type; Ty : Entity_Id; N : Node_Id);
   --  Check a value V against the range bounds or apply modulo of the type Ty,
   --  if V is an integer, signaling errors for node N.

   function Int_Value (I : Big_Integer; Ty : Entity_Id) return Value_Type is
      (Scalar_Value ((K => Integer_K, Integer_Content => I), Retysp (Ty)));

   function Integer_Value
     (I     : Big_Integer;
      Ty    : Entity_Id;
      N     : Node_Id;
      Check : Boolean := True)
      return Value_Type;
   --  Construct an integer value after checking against type bounds or
   --  applying modulo for type Ty, signaling errors for node N.

   function Copy (V : Value_Type) return Value_Type;
   --  Make a copy of a value

   function Copy
     (F : Entity_To_Value_Maps.Map)
      return Entity_To_Value_Maps.Map;
   --  Make a copy of record fields

   function Copy
     (A : Big_Integer_To_Value_Maps.Map)
      return Big_Integer_To_Value_Maps.Map;

   function Default_Value
     (Ty    : Node_Id;
      Check : Boolean := True) return Value_Type;
   --  Return the type default value

   function Fuzz_Value (Ty : Node_Id) return Value_Type;
   --  Return a random value amongst those that often highlight bugs

   function Enum_Entity_To_Integer (E : Entity_Id) return Uint;
   --  Convert an enum entity (enum literal entity or character literal) to an
   --  integer (enum pos for enumerations, character pos for characters).

   function "=" (F1, F2 : Entity_To_Value_Maps.Map) return Boolean;

   procedure Cleanup_Counterexample_Value (V : in out Value_Type; N : Node_Id);
   --  Clean-up counterexample values so they can be used by the RAC.
   --  Call RAC_Unsupported if the counterexample value is unsupported yet, and
   --  Exn_RAC_Stuck if the value is incomplete.

   --------------------------------
   -- Runtime control exceptions --
   --------------------------------

   Exn_RAC_Exit : exception;
   --  Signal a loop exit

   Exn_RAC_Return : exception;
   --  Signal the return from a subprogram

   procedure RAC_Return (V : Opt_Value_Type) with No_Return;
   --  Return from subprogram, optionally with some return value

   function Flush_RAC_Return return Opt_Value_Type;
   --  Get and reset return value from last call to RAC_Return

   ---------------------------
   -- RAC result exceptions --
   ---------------------------

   Exn_RAC_Failure : exception;
   --  Raised for invalid assertions (always use RAC_Failure to ensure
   --  Flush_Exn_RAC_Result).

   Exn_RAC_Stuck : exception;
   --  Raised for invalid assumption (always use RAC_Stuck or related to ensure
   --  Flush_Exn_RAC_Result).

   Exn_RAC_Incomplete : exception;
   --  Raise when execution or RAC incomplete (always use RAC_Incomplete or
   --  related to ensure Flush_Exn_RAC_Result).

   function Peek_Exn_RAC_Result return Result;
   --  Get the result from the last call to RAC_Failure, RAC_Stuck,
   --  RAC_Incomplete, or related.

   function Flush_Exn_RAC_Result return Result;
   --  Get and reset the result from the last call to RAC_Failure, RAC_Stuck,
   --  RAC_Incomplete, or related.

   type Result_Option (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Result;
         when False =>
            null;
      end case;
   end record;
   --  An optional result

   function Some_Result (R : Result) return Result_Option is
     (Present => True, Content => R);

   function No_Result return Result_Option is
     (Present => False);

   Exn_RAC_Result : Result_Option;
   --  The result of a assertion or assumption failure, set by RAC_Failure,
   --  RAC_Stuck, or RAC_Stuck_For_Failure, retrieved by Flush_RAC_Result.

   procedure RAC_Failure (N : Node_Id; K : VC_Kind) with No_Return;
   --  Raise Exn_RAC_Failure and set result, i.e. the RAC execution failed
   --  due to a false check.

   procedure RAC_Incomplete (Reason : String) with No_Return;
   --  Raise Exn_RAC_Incomplete and set result, i.e. the RAC execution could
   --  not complete due to technical or theoretical limitations.

   procedure RAC_Unsupported (Str : String; Str1 : String) with No_Return;
   --  Raise Exn_RAC_Incomplete and set result, i.e. the RAC execution could
   --  not complete due to unsupported or unimplemented features.

   Exn_RAC_Return_Value : access Opt_Value_Type;
   --  The return value, set by RAC_Return, retrieved by Flush_RAC_Return

   --------------------------------------------
   -- The evaluation environment and context --
   --------------------------------------------

   package Node_To_Value is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Value_Type,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   package Entity_Bindings is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Value_Access,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Flat mapping of variables to bindings

   type Scopes is record
      Bindings         : Entity_Bindings.Map;
      Old_Attrs        : Node_To_Value.Map;
      Loop_Entry_Attrs : Node_To_Value.Map;
   end record;
   --  A scope is a flat mapping of variable (defining identifiers) to bindings
   --  and a mapping of old and loop entry values of expressions.

   function To_String (S : Scopes) return String;

   package Environments is new Ada.Containers.Vectors
     (Index_Type   => Natural,
      Element_Type => Scopes,
      "="          => "=");
   --  An execution environment is a stack of scopes

   function To_String (E : Environments.Vector) return String
     with Unreferenced;

   procedure Set_Value
     (S : in out Scopes;
      E :        Entity_Id;
      V :        Value_Access);
   --  Set (or update) the value of an identifier in a scope

   procedure Update_Value
     (Env : in out Environments.Vector;
      E   :        Entity_Id;
      V   :        Value_Access);
   --  Search and update the value of an identifier in its scope. If not found,
   --  it is assumed to be a global constant without variable input and set.

   type Context is record
      Env              : Environments.Vector;
      --  The variable environment
      Cntexmp          : Cntexample_File_Maps.Map;
      --  The counterexample
      Fuel             : Fuel_Access := null;
      --  If Fuel is non-negative, it is decreased at the execution of each
      --  expression and statement and the execution terminates as incomplete
      --  when out of fuel.
      Rem_Stack_Height : Integer;
      --  If Rem_Stack_Height is non-negative, it is decreased at the beginning
      --  of the execution of each call to a function or procedure, and
      --  decreased at the end. When it reaches zero, the execution terminates
      --  as incomplete.
      Do_Sideeffects   : Boolean;
      --  Really do side-effects when interpreting built-ins such as Put_Line
   end record;
   --  The execution context

   Ctx : Context;
   --  Lo and behold! The global execution context

   procedure Evaluate_Attribute_Prefix_Values
     (Attr_Name : Name_Id;
      Prefixes  : Node_Sets.Set)
     with Pre => Attr_Name in Snames.Name_Old | Snames.Name_Loop_Entry;
   --  For each node in Prefixes, evaluate it and add its value to the
   --  appropriate map from prefixes to their values.

   -------------------
   -- Value oracles --
   -------------------

   function Can_Get (N : Node_Id) return Boolean is
     (Nkind (N) in N_Defining_Identifier | N_Identifier | N_Expanded_Name)
   with
     Ghost => True;
   --  Predicate for nodes, for which the counterexample may have a value

   function Get_Cntexmp_Value
     (N       : Node_Id;
      Cntexmp : Cntexample_File_Maps.Map)
      return Opt_Value_Type
   with
     Pre => Can_Get (N);
   --  Get the value of variable N from the counterexample

   type Value_Origin is
     (From_Counterexample, From_Expr, From_Type_Default, From_Fuzzer);
   --  The origin of a value in a call to Get

   function Get_Value
     (N           :     Node_Id;
      Ex          :     Node_Id;
      Use_Default :     Boolean;
      Use_Fuzzing :     Boolean;
      Origin      : out Value_Origin)
      return Value_Type
   with
     Pre => Can_Get (N);
   --  Get a value for variable N using the first successful of the following
   --  strategies:
   --  1) from the fuzzer (if Use_Fuzzing is True),
   --  2) from the counterexample in the context,
   --  3) from the evaluation of an expression Ex (if present),
   --  4) or the type default (if Use_Default is True)
   --  If neither of the strategies provides a value, the function signals
   --  RAC_Incomplete.

   ---------------------------------------
   -- Check the validity of annotations --
   ---------------------------------------

   procedure Get_Bounds (N : Node_Id; Low, High : out Big_Integer);
   --  Get the low and high bounds of node N

   procedure Check_Node
     (N    : N_Subexpr_Id;
      Desc : String;
      K    : VC_Kind);

   procedure Check_List
     (L   : Node_Lists.List;
      Msg : String;
      K   : VC_Kind);
   --  Check the validity of formulas L

   type Ulargest is mod 2 ** 128;
   --  The largest modular type to execute modulo operators

   procedure Iterate_Loop_Param_Spec
     (Param_Spec : Node_Id; Iteration : not null access procedure);
   --  Iterate a loop parameter specification by calling Iteration

   function Match_Alternative
     (V  : Value_Type;
      Ch : Node_Id) return Boolean;
   --  Test V against Ch, return true if V is:
   --  * in the range described by Ch
   --  * of the type denoted by Ch
   --  * equal to the value of Ch
   --  * falls in the others alternative. This is only used in case statements
   --    or expressions.
   --  Return false otherwise.

   procedure Match_Case_Alternative (N : Node_Id; A : out Node_Id)
     with Pre => Nkind (N) in N_Case_Expression | N_Case_Statement;
   --  Test the expression against each case choice expression. Fill A
   --  with the matching alternative.

   function RAC_Expr
     (N   : N_Subexpr_Id;
      Ty0 : Entity_Id := Empty) return Value_Type;
   --  Evaluate node N to a value

   function RAC_Expr_LHS (N : N_Subexpr_Id) return Value_Access;
   --  Evaluate node N to a value pointer for the left-hand side of an
   --  assignment.

   procedure RAC_Statement (N : Node_Id);
   --  RAC execution of a statement N

   procedure RAC_Pragma (N : N_Pragma_Id);
   --  RAC execution of a pragma N

   procedure RAC_Node (N : Node_Id);
   --  RAC execution of node N

   procedure RAC_List (L : List_Id);
   --  RAC execution of list L

   procedure RAC_Decl (Decl : Node_Id);
   --  Add a declaration to the first scope of the context environment

   procedure RAC_Decls (Decls : List_Id);
   --  Add declarations to the first scope of the context environment

   function RAC_Call
     (N            : Node_Id;
      E            : Entity_Id;
      Is_Main      : Boolean := False;
      Fuzz_Formals : Boolean := False)
      return Opt_Value_Type;
   --  RAC execution of a call to E with parameters in Scope. If Is_Main is
   --  True, the argument values are taken from the counterexample and failing
   --  preconditions trigger stuck instead of failure. If Fuzz_Formals is set
   --  to True, use the fuzzer to generated to values for the function's
   --  parameter.

   No_Builtin : exception;
   --  Raisen when the entity is not builtin in RAC_Call_Builtin

   function RAC_Call_Builtin
     (E              : Entity_Id;
      Sc             : Scopes;
      Do_Sideeffects : Boolean)
      return Opt_Value_Type;
   --  Execute a builtin E, if it exists, or raise No_Builtin otherwise

   procedure Init_Global
     (N             :     Node_Id;
      Use_Expr      :     Boolean;
      Use_Fuzzing   :     Boolean;
      Default_Value :     Boolean;
      Val           : out Value_Access;
      Descr         :     String);
   --  Initialize a global variable from the appropriate source. The decision
   --  of the source of the value is made by Get_Value.

   function Param_Scope (Call : Node_Id) return Scopes;
   --  Create a scope of parameters for a call Call

   procedure Slide
     (V : in out Value_Type;
      E :        Entity_Id)
     with Pre => V.K = Array_K
     and then Is_Array_Type (E)
     and then Is_Constrained (E);
   --  Slide the values of Array_Values of V to the correct bounds described in
   --  E if necessary.

   procedure Copy_Out_Parameters
     (Call :        Node_Id;
      Sc   : in out Scopes);
   --  Copy scalar values of out and in_out parameters from the parameter scope
   --  Sc to the environment.

   ---------------------------
   -- Debugging auxiliaries --
   ---------------------------

   Do_RAC_Info_Env  : constant Boolean :=
     Ada.Environment_Variables.Value ("GNAT2WHY_RAC_INFO", "off") = "on";
   --  Enable RAC_Info by environment variable GNAT2WHY_RAC_INFO

   Do_RAC_Trace : constant Boolean :=
     Ada.Environment_Variables.Value ("GNAT2WHY_RAC_TRACE", "off") = "on";
   --  Enable RAC_Trace by environment variable GNAT2WHY_RAC_TRACE

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Info (Msg : String) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) with
      Inline;
   --  Trace the RAC execution

   procedure Call_Stack;
   --  Print the current call stack

   ---------
   -- "=" --
   ---------

   function "=" (F1, F2 : Entity_To_Value_Maps.Map) return Boolean is
      use Entity_To_Value_Maps;
      C2 : Cursor;
   begin
      pragma Assert (Length (F1) = Length (F2));
      for C1 in F1.Iterate loop
         C2 := F2.Find (Key (C1));

         if not Has_Element (C2)
            or else F1 (C1).all /= F2 (C2).all
         then
            return False;
         end if;
      end loop;
      return True;
   end "=";

   -------------------
   -- Boolean_Value --
   -------------------

   function Boolean_Value (B : Boolean; Ty : Entity_Id) return Value_Type is
     (Scalar_Value ((K => Enum_K, Enum_Entity => Boolean_Literals (B)), Ty));

   ----------------
   -- Call_Stack --
   ----------------

   procedure Call_Stack is
      Trace  : GNAT.Traceback.Tracebacks_Array (1 .. 1_000);
      Length : Natural;
   begin
      GNAT.Traceback.Call_Chain (Trace, Length);
      Write_Line
        (GNAT.Traceback.Symbolic.Symbolic_Traceback (Trace (1 .. Length)));
   end Call_Stack;

   ---------------------
   -- Character_Value --
   ---------------------

   function Character_Value
     (C : Character; Ty : Entity_Id)
      return Value_Type
   is
      CC : constant Char_Code := Get_Char_Code (C);
   begin
      Set_Character_Literal_Name (CC);

      return
        Enum_Value
          (Make_Character_Literal
             (No_Location, Name_Find, UI_From_CC ((CC))),
           Ty);
   end Character_Value;

   --------------------------
   -- Check_Supported_Type --
   --------------------------

   procedure Check_Supported_Type (Ty : Entity_Id) is
   begin
      --  We do not support the 'Constrained attribute yet

      if Has_Discriminants (Ty) and then Has_Defaulted_Discriminants (Ty) then
         RAC_Unsupported ("Type has mutable discrimants", Ty);
      end if;
      if Has_Predicates (Ty) then
         RAC_Unsupported ("Type has predicates", Ty);
      end if;
      if Has_Invariants_In_SPARK (Ty) then
         RAC_Unsupported ("Type has invariants", Ty);
      end if;
      if Is_Class_Wide_Type (Ty) then
         RAC_Unsupported ("Type is class wide type", Ty);
      end if;
      if Has_Predicates (Ty) and then not Has_Static_Predicate (Ty) then
         RAC_Unsupported ("Type has dynamic predicate aspect", Ty);
      end if;
      if Is_Floating_Point_Type (Ty) then
         RAC_Unsupported ("Floating point type", Ty);
      end if;
      if Is_Array_Type (Ty)
        and then Number_Dimensions (Ty) > 1
      then
         RAC_Unsupported ("Multidimensional array type", Ty);
      end if;
   end Check_Supported_Type;

   -------------------------
   -- Check_Fuel_Decrease --
   -------------------------

   procedure Check_Fuel_Decrease
     (Fuel   : Fuel_Access;
      Amount : Fuel_Type := 1) is
   begin
      if Fuel /= null then
         if Fuel.all = 0 then
            RAC_Incomplete ("out of fuel");
         elsif Fuel.all > 0 then
            Fuel.all := Fuel.all - Amount;
         end if;
      end if;
   end Check_Fuel_Decrease;

   -------------------
   -- Check_Integer --
   -------------------

   procedure Check_Integer (I : Big_Integer; Ty : Entity_Id; N : Node_Id) is
      Fst, Lst : Big_Integer;
      Kind     : VC_Kind;
      Desc     : constant String :=
        "Check integer " & To_String (I)
        & " of type " & Get_Name_String (Chars (Ty));
   begin
      Get_Integer_Type_Bounds (Ty, Fst, Lst);
      Kind :=
        (if Is_Base_Type (Ty) then VC_Overflow_Check else VC_Range_Check);

      if not In_Range (I, Fst, Lst) then
         RAC_Info (Desc, "has failed as " & VC_Kind'Image (Kind), N);
         RAC_Failure (N, Kind);
      end if;
   end Check_Integer;

   procedure Check_Integer (V : Value_Type; Ty : Entity_Id; N : Node_Id) is
   begin
      if V.K = Scalar_K
        and then V.Scalar_Content /= null
        and then V.Scalar_Content.K = Integer_K
      then
         Check_Integer (V.Scalar_Content.Integer_Content, Ty, N);
      end if;
   end Check_Integer;

   ----------------
   -- Check_List --
   ----------------

   procedure Check_List
     (L   : Node_Lists.List;
      Msg : String;
      K   : VC_Kind)
   is
   begin
      for N of L loop
         Check_Node (N, Msg, K);
      end loop;
   end Check_List;

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node
     (N    : N_Subexpr_Id;
      Desc : String;
      K    : VC_Kind)
   is
      V : Value_Type;
   begin
      RAC_Trace ("check node " & Node_Kind'Image (Nkind (N)));
      V := RAC_Expr (N);

      if Value_Boolean (V) then
         RAC_Info (Capitalize (Desc), "is OK", N);
      else
         RAC_Info (Capitalize (Desc), "failed", N);
         RAC_Failure (N, K);
      end if;
   end Check_Node;

   ----------------------------------
   -- Cleanup_Counterexample_Value --
   ----------------------------------

   procedure Cleanup_Counterexample_Value (V : in out Value_Type; N : Node_Id)
   is
   begin
      Check_Supported_Type (V.AST_Ty);

      case V.K is
         when Scalar_K =>

            --  Check that we have an actual value for the scalar

            if (V.Initialized_Attr.Present
                and then not V.Initialized_Attr.Content)
              or else V.Scalar_Content = null
            then
               RAC_Unsupported ("uninitialized scalar", N);

            --  Real types are not supported yet

            elsif V.Scalar_Content.K not in Integer_K .. Enum_K then
               RAC_Unsupported
                 ("value of real type " & Full_Name (V.AST_Ty), N);
            end if;

         when Record_K =>

            --  Check that we have values for all components and discriminants.
            --  Delete components which are not present in the type.

            if Has_Discriminants (V.AST_Ty) then
               declare
                  Discr : Entity_Id := First_Discriminant
                    (Root_Retysp (V.AST_Ty));
                  Elmt  : Elmt_Id :=
                    (if Is_Constrained (V.AST_Ty)
                     then First_Elmt (Discriminant_Constraint (V.AST_Ty))
                     else No_Elmt);
               begin
                  while Present (Discr) loop
                     if not V.Record_Fields.Contains (Discr) then
                        if Is_Constrained (V.AST_Ty) then
                           V.Record_Fields.Insert
                             (Discr,
                              new Value_Type'
                                (RAC_Expr
                                     (Node (Elmt), Retysp (Etype (Discr)))));
                        else
                           RAC_Stuck
                             ("missing value for discriminant "
                              & Source_Name (Discr)
                              & " in " & Full_Name (V.AST_Ty));
                        end if;
                     else
                        Cleanup_Counterexample_Value
                          (V.Record_Fields (Discr).all, N);
                     end if;

                     Next_Discriminant (Discr);
                     if Is_Constrained (V.AST_Ty) then
                        Next_Elmt (Elmt);
                     end if;
                  end loop;
               end;
            end if;

            for Comp of Get_Component_Set (V.AST_Ty) loop
               if Component_Is_Removed_In_Type
                 (V.AST_Ty, Comp, V.Record_Fields)
               then
                  V.Record_Fields.Exclude (Comp);
               elsif Is_Type (Comp) then
                  RAC_Unsupported
                    ("invisible component from type " & Full_Name (Comp),
                     N);
               elsif not V.Record_Fields.Contains (Comp) then
                  RAC_Stuck
                    ("missing value for field "
                     & Source_Name (Comp) & " of type "
                     & Source_Name (Original_Declaration (Comp)));
               elsif Has_Discriminant_Dependent_Constraint (Comp) then
                  RAC_Unsupported
                    ("discriminant dependant component " & Source_Name (Comp),
                     N);
               else
                  Cleanup_Counterexample_Value (V.Record_Fields (Comp).all, N);
               end if;
            end loop;

         when Array_K =>

            declare
               Type_Fst : Big_Integer;
               Type_Lst : Big_Integer;
               Fst, Lst : Big_Integer;

            begin
               Get_Bounds
                 (Get_Range (First_Index (V.AST_Ty)), Type_Fst, Type_Lst);

               --  For constrained arrays, fill the bounds

               if Is_Constrained (V.AST_Ty) then
                  Fst := Type_Fst;
                  Lst := Type_Lst;

                  if V.First_Attr.Present then
                     Slide (V, V.AST_Ty);
                  end if;

                  V.First_Attr := (True, Fst);
                  V.Last_Attr := (True, Lst);

               --  For other arrays, check that the bounds are provided, and
               --  that they are in the index type.

               else
                  if not V.First_Attr.Present
                    or else not V.Last_Attr.Present
                  then
                     RAC_Stuck
                       ("Missing bound in unconstrained array"
                        & " counterexample");
                  end if;

                  Fst := V.First_Attr.Content;
                  Lst := V.Last_Attr.Content;

                  if Fst <= Lst
                    and then (Fst < Type_Fst or else Lst > Type_Lst)
                  then
                     RAC_Stuck
                       ("Incorrect bound in unconstrained array"
                        & " counterexample");
                  end if;
               end if;

               --  Check the supplied values. Delete out-of-bounds values.

               declare
                  use Big_Integer_To_Value_Maps;
                  C : Cursor := First (V.Array_Values);

               begin
                  while Has_Element (C) loop
                     declare
                        Idx : Big_Integer renames Key (C);
                        Val : Value_Access renames Element (C);

                     begin
                        if not (Fst <= Idx and then Idx <= Lst) then
                           declare
                              Nxt : constant Cursor := Next (C);
                           begin
                              V.Array_Values.Delete (C);
                              C := Nxt;
                           end;

                        else
                           Cleanup_Counterexample_Value (Val.all, N);
                           Next (C);
                        end if;
                     end;
                  end loop;
               end;

               if V.Array_Others /= null then
                  Cleanup_Counterexample_Value (V.Array_Others.all, N);
               end if;
            end;

         when Multidim_K =>
            RAC_Unsupported ("multidimensional array type", N);

         when Access_K =>
            RAC_Unsupported ("value of an access type", N);
      end case;
   end Cleanup_Counterexample_Value;

   ----------
   -- Copy --
   ----------

   function Copy
     (F : Entity_To_Value_Maps.Map) return Entity_To_Value_Maps.Map
   is
      use Entity_To_Value_Maps;
      Res : Map;
   begin
      for C in F.Iterate loop
         Res.Insert (Key (C), new Value_Type'(Copy (F (C).all)));
      end loop;
      return Res;
   end Copy;

   function Copy
     (A : Big_Integer_To_Value_Maps.Map) return Big_Integer_To_Value_Maps.Map
   is
      use Big_Integer_To_Value_Maps;
      Res : Map;
   begin
      for C in A.Iterate loop
         Res.Insert (Key (C), new Value_Type'(Copy (A (C).all)));
      end loop;
      return Res;
   end Copy;

   function Copy (V : Value_Type) return Value_Type is
   begin
      --  ??? gnatcov complains if this is an expression function (V330-044)
      return
        (case V.K is
            when Record_K   =>
               (V with delta Record_Fields => Copy (V.Record_Fields)),
            when Array_K    =>
               (V with delta
                    Array_Values => Copy (V.Array_Values),
                    Array_Others =>
                      (if V.Array_Others = null then null
                       else new Value_Type'(Copy (V.Array_Others.all)))),
            when Scalar_K   =>
               (V with delta Scalar_Content =>
                   (if V.Scalar_Content = null then null
                    else new Scalar_Value_Type'(V.Scalar_Content.all))),
            when Access_K   =>
               (V with delta Designated_Value =>
                   (if V.Designated_Value = null then null
                    else new Value_Type'(Copy (V.Designated_Value.all)))),
           when Multidim_K => V);
   end Copy;

   -------------------------
   -- Copy_Out_Parameters --
   -------------------------

   procedure Copy_Out_Parameters
     (Call :        Node_Id;
      Sc   : in out Scopes)
   is
      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Do the copy out for one parameter

      -------------------
      -- Process_Param --
      -------------------

      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id) is
      begin
         if Is_Scalar_Type (Etype (Formal))
           and then Ekind (Formal) in E_In_Out_Parameter | E_Out_Parameter
         then
            RAC_Expr_LHS (Actual).all :=
              Sc.Bindings (Formal).all;
         end if;
      end Process_Param;

      procedure Iterate_Call is new Iterate_Call_Parameters (Process_Param);

   --  Start of processing for Copy_Out_Parameters

   begin
      Iterate_Call (Call);
   end Copy_Out_Parameters;

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value
     (Ty : Node_Id; Check : Boolean := True) return Value_Type
   is
      Rep_Ty : constant Entity_Id := Retysp (Ty);
   begin

      if Is_Integer_Type (Rep_Ty) then
         --  0 or Ty'First
         declare
            Fst, Lst, I : Big_Integer;
            Zero        : constant Big_Integer := 0;
         begin
            Get_Integer_Type_Bounds (Rep_Ty, Fst, Lst);
            I := (if In_Range (Zero, Fst, Lst) then Zero else Fst);
            return Integer_Value (I, Rep_Ty, Empty, Check => Check);
         end;

      elsif Is_Character_Type (Rep_Ty) then
         return Character_Value ('a', Rep_Ty);

      elsif Is_Enumeration_Type (Rep_Ty) then
         return Enum_Value (First_Literal (Rep_Ty), Rep_Ty);

      elsif Is_Array_Type (Rep_Ty) then
         declare
            Fst, Lst : Big_Integer;
            Other    : Value_Access;
            U_Fst    : Uint;
            U_Lst    : Uint;

         begin
            --  Use static array type bounds or index type bounds as default

            Find_First_Static_Range (First_Index (Rep_Ty), U_Fst, U_Lst);
            Fst := From_String (UI_Image (U_Fst, Decimal));
            Lst := From_String (UI_Image (U_Lst, Decimal));

            if not Is_Constrained (Rep_Ty) then
               Lst := Fst;
            end if;

            if Has_Default_Aspect (Rep_Ty) then
               Other := new Value_Type'
                 (RAC_Expr (Default_Aspect_Component_Value (Rep_Ty)));
            else
               Other := new Value_Type'
                 (Default_Value (Component_Type (Rep_Ty)));
            end if;

            return Array_Value
              (Fst, Lst, Big_Integer_To_Value_Maps.Empty, Other, Rep_Ty);
         end;

      elsif Is_Record_Type (Rep_Ty) then
         declare
            F     : Entity_To_Value_Maps.Map;
            Discr : Entity_Id;
            Elmt  : Elmt_Id;
         begin
            if Has_Discriminants (Rep_Ty) then
               Discr := First_Discriminant (Root_Retysp (Rep_Ty));

               --  For constrained subtypes get the discriminant values from
               --  the type.

               if Is_Constrained (Rep_Ty) then
                  Elmt := First_Elmt (Discriminant_Constraint (Rep_Ty));
                  while Present (Discr) loop
                     F.Insert
                       (Discr,
                        new Value_Type'
                          (RAC_Expr (Node (Elmt), Retysp (Etype (Discr)))));
                     Next_Discriminant (Discr);
                     Next_Elmt (Elmt);
                  end loop;

               --  Use default values for discriminants

               else
                  while Present (Discr) loop
                     F.Insert
                       (Discr, new Value_Type'(Default_Value (Etype (Discr))));
                     Next_Discriminant (Discr);
                  end loop;
               end if;
            end if;

            for Comp of Get_Component_Set (Rep_Ty) loop
               if Component_Is_Removed_In_Type (Rep_Ty, Comp, F) then
                  null;
               elsif Is_Type (Comp) then
                  RAC_Unsupported
                    ("private part in type " & Full_Name (Comp), Rep_Ty);

               --  Use the default value of the component if any

               elsif Present (Expression (Enclosing_Declaration (Comp))) then
                  F.Insert
                    (Comp,
                     new Value_Type'
                       (RAC_Expr (Expression (Enclosing_Declaration (Comp)),
                        Retysp (Etype (Comp)))));
               else
                  F.Insert
                    (Comp, new Value_Type'(Default_Value (Etype (Comp))));
               end if;
            end loop;

            return Record_Value (F, Rep_Ty);
         end;

      else
         RAC_Unsupported ("Default_Value", Ty);
      end if;
   end Default_Value;

   -----------------
   -- Do_RAC_Info --
   -----------------

   function Do_RAC_Info return Boolean is
     (Gnat2Why_Opts.Reading.Debug_Mode or else Do_RAC_Info_Env);

   ----------------------------
   -- Enum_Entity_To_Integer --
   ----------------------------

   function Enum_Entity_To_Integer (E : Entity_Id) return Uint is
   begin
      if Nkind (E) = N_Character_Literal then
         return Char_Literal_Value (E);
      elsif Is_Enumeration_Type (Etype (E)) then
         return Enumeration_Pos (E);
      else
         raise Program_Error with "Enum_Entity_To_Integer";
      end if;
   end Enum_Entity_To_Integer;

   ----------------
   -- Enum_Value --
   ----------------

   function Enum_Value (I : Uint; Ty : Entity_Id) return Value_Type is
      Lit : Node_Id;
   begin
      Check_Supported_Type (Ty);
      Lit := Get_Enum_Lit_From_Pos (Ty, I);
      return Scalar_Value
        ((K          => Enum_K,
          Enum_Entity =>
            (if Nkind (Lit) = N_Character_Literal then Lit else Entity (Lit))),
         Ty);
   exception
      when Constraint_Error =>
         RAC_Stuck ("Enum_Value: value outside of range");
   end Enum_Value;

   --------------------------------------
   -- Evaluate_Attribute_Prefix_Values --
   --------------------------------------

   procedure Evaluate_Attribute_Prefix_Values
     (Attr_Name : Name_Id;
      Prefixes  : Node_Sets.Set)
   is
   begin
      for P of Prefixes loop
         declare
            Val : constant Value_Type := RAC_Expr (P);
            --  While evaluating the value we might modify the global context,
            --  so first evaluate the value and only then add it to the
            --  context.

            Inserted : Boolean;
            Position : Node_To_Value.Cursor;

         begin
            if Attr_Name = Name_Old then
               Ctx.Env (Ctx.Env.First).Old_Attrs.Insert
                 (P, Val, Position, Inserted);

            else pragma Assert (Attr_Name = Name_Loop_Entry);
               Ctx.Env (Ctx.Env.First).Loop_Entry_Attrs.Insert
                 (P, Val, Position, Inserted);

            end if;
         end;
      end loop;
   end Evaluate_Attribute_Prefix_Values;

   ------------------
   -- Find_Binding --
   ------------------

   function Find_Binding (E : Entity_Id) return Value_Access
   is
      C : Entity_Bindings.Cursor;
      B : Value_Access;
   begin
      for Scope of Ctx.Env loop
         C := Scope.Bindings.Find (E);

         if Entity_Bindings.Has_Element (C) then
            return Scope.Bindings (C);
         end if;
      end loop;

      --  Lazily initialize globals that were not initialized by Global_Scope
      Init_Global (N             => E,
                   Use_Expr      => True,
                   Use_Fuzzing   => False,
                   Default_Value => False,
                   Val           => B,
                   Descr         => "constant without variable input");

      return B;
   end Find_Binding;

   -----------------------
   -- Flush_RAC_Failure --
   -----------------------

   function Flush_Exn_RAC_Result return Result is
      Res : Result;
   begin
      if not Exn_RAC_Result.Present then
         raise Program_Error with "Flush_Exn_RAC_Result";
      end if;

      Res := Exn_RAC_Result.Content;
      Exn_RAC_Result := No_Result;
      return Res;
   end Flush_Exn_RAC_Result;

   ----------------------
   -- Flush_RAC_Return --
   ----------------------

   function Flush_RAC_Return return Opt_Value_Type is
      V : Opt_Value_Type;
   begin
      if Exn_RAC_Return_Value = null then
         raise Program_Error with "Flush_RAC_Return";
      end if;

      V := Exn_RAC_Return_Value.all;
      Exn_RAC_Return_Value := null;
      return V;
   end Flush_RAC_Return;

   ----------------
   -- Fuzz_Value --
   ----------------

   function Fuzz_Value (Ty : Node_Id) return Value_Type is
      Rep_Ty : constant Entity_Id := Retysp (Ty);
   begin
      if Is_Integer_Type (Rep_Ty) then
         return Fuzz_Integer_Value (Rep_Ty);
      elsif Is_Record_Type (Rep_Ty) then
         return Fuzz_Record_Value (Rep_Ty);
      else
         RAC_Unsupported ("Fuzz_Value", Ty);
      end if;
   end Fuzz_Value;

   -----------------------
   -- Get_Cntexmp_Value --
   -----------------------

   function Get_Cntexmp_Value
     (N       : Node_Id;
      Cntexmp : Cntexample_File_Maps.Map)
      return Opt_Value_Type
   is
      Filename : constant String  := File_Name (Sloc (N));
      Line     : constant Integer :=
        Integer (Get_Physical_Line_Number (Sloc (N)));
      Files_C  : constant Cntexample_File_Maps.Cursor :=
        Cntexmp.Find (Filename);
      Obj      : constant Entity_Id :=
        (if Nkind (N) in N_Identifier | N_Expanded_Name then Entity (N)
         else N);

   begin
      if not Cntexample_File_Maps.Has_Element (Files_C) then
         return No_Value;
      end if;

      declare
         Lines   : Cntexample_Lines renames Cntexmp (Files_C);
         Lines_C : constant Cntexample_Line_Maps.Cursor :=
           Lines.Other_Lines.Find (Line);
         Val     : Opt_Value_Type;
      begin
         if not Cntexample_Line_Maps.Has_Element (Lines_C) then
            return No_Value;
         end if;

         Val := Get_Counterexample_Value
           (Obj, Cntexample_Line_Maps.Element (Lines_C));

         if Val.Present then
            Cleanup_Counterexample_Value (Val.Content, N);
         end if;
         return Val;
      end;
   end Get_Cntexmp_Value;

   ----------------
   -- Get_Bounds --
   ----------------

   procedure Get_Bounds (N : Node_Id; Low, High : out Big_Integer) is

      function To_Big_Integer (N : Node_Id) return Big_Integer;

      function To_Big_Integer (N : Node_Id) return Big_Integer is
      begin
         if SPARK_Atree.Compile_Time_Known_Value (N) then
            return From_String (UI_Image (SPARK_Atree.Expr_Value (N)));
         else
            return Value_Enum_Integer (RAC_Expr (N));
         end if;
      end To_Big_Integer;

   --  Start of processing for Get_Bounds

   begin
      Low := To_Big_Integer (Low_Bound (N));
      High := To_Big_Integer (High_Bound (N));
   end Get_Bounds;

   -----------------------------
   -- Get_Integer_Type_Bounds --
   -----------------------------

   procedure Get_Integer_Type_Bounds
     (Ty       :     Entity_Id;
      Fst, Lst : out Big_Integer)
   is
   begin
      Get_Bounds (Get_Range (Ty), Fst, Lst);
   end Get_Integer_Type_Bounds;

   ---------------
   -- Get_Value --
   ---------------

   function Get_Value
     (N           :     Node_Id;
      Ex          :     Node_Id;
      Use_Default :     Boolean;
      Use_Fuzzing :     Boolean;
      Origin      : out Value_Origin)
      return Value_Type
   is
      OV  : Opt_Value_Type;
      Res : Value_Type;
   begin
      if Use_Fuzzing then
         Res := Fuzz_Value (Etype (N));
         Origin := From_Fuzzer;
      else
         OV := Get_Cntexmp_Value (N, Ctx.Cntexmp);
         if OV.Present then
            Res := OV.Content;
            Origin := From_Counterexample;
         elsif Present (Ex) then
            Res := RAC_Expr (Ex);
            Origin := From_Expr;
         elsif Use_Default then
            Res := Default_Value (Etype (N));
            Origin := From_Type_Default;
         else
            RAC_Incomplete
              ("No counterexample value for program parameter " &
                 Get_Name_String (Chars (N)) & "(" & Node_Id'Image (N) & ")");
         end if;
      end if;

      RAC_Info
        ("Get " & Get_Name_String (Chars (N)) &
           " (" & Value_Origin'Image (Origin) & ")" &
           " = " & To_String (Res));
      return Res;
   end Get_Value;

   -----------------
   -- Init_Global --
   -----------------

   procedure Init_Global
     (N             :     Node_Id;
      Use_Expr      :     Boolean;
      Use_Fuzzing   :     Boolean;
      Default_Value :     Boolean;
      Val           : out Value_Access;
      Descr         :     String)
   is
      Origin : Value_Origin;
      Expr   : constant Node_Id :=
        (if Use_Expr and then not Is_Formal (N)
         then Expression (Enclosing_Declaration (N)) else Empty);
   begin

      Val := new Value_Type'
        (Get_Value (N, Expr, Default_Value, Use_Fuzzing, Origin));

      Ctx.Env (Ctx.Env.Last).Bindings.Insert (N, Val);

      RAC_Trace ("Initialize global " & Descr & " "
                 & Get_Name_String (Chars (N)) & " to "
                 & To_String (Val.all) & " " & Value_Origin'Image (Origin));
   end Init_Global;

   -------------------
   -- Integer_Value --
   -------------------

   function Integer_Value
     (I     : Big_Integer;
      Ty    : Entity_Id;
      N     : Node_Id;
      Check : Boolean := True)
      return Value_Type
   is
      Res : Big_Integer := I;
   begin
      if Is_Modular_Integer_Type (Ty) then
         if No (Modulus (Ty)) then
            --  ??? TODO Modulus 0 for System.Address in
            --      O226-018__address/src/worker_pack__worker_init
            RAC_Unsupported ("Modular integer zero", Ty);
         end if;
         Res := Res mod From_String (UI_Image (Modulus (Ty)));
      elsif Check then
         Check_Integer (I, Ty, N);
      end if;
      return Scalar_Value ((K => Integer_K, Integer_Content => Res), Ty);
   end Integer_Value;

   function Integer_Value (I : Big_Integer; N : Node_Id) return Value_Type is
   begin
      return Integer_Value (I, Retysp (Etype (N)), N);
   end Integer_Value;

   -----------------------------
   -- Iterate_Loop_Param_Spec --
   -----------------------------

   procedure Iterate_Loop_Param_Spec
     (Param_Spec : Node_Id; Iteration : not null access procedure)
   is
      Def          : constant Node_Id :=
        Discrete_Subtype_Definition (Param_Spec);
      Actual_Range : constant Node_Id := Get_Range (Def);
      Low_Bnd      : constant Node_Id := Low_Bound (Actual_Range);
      Low          : constant Value_Type := RAC_Expr (Low_Bnd);
      High         : constant Value_Type :=
        RAC_Expr (High_Bound (Actual_Range));
      Id           : constant Entity_Id := Defining_Identifier (Param_Spec);
      Iter_Typ     : constant Entity_Id := Etype (Low_Bnd);
      Curr, Stop   : Big_Integer;
      Step         : Big_Integer := To_Big_Integer (1);
      Test         : -- Test for Curr and Stop during iteration
        not null access function (L, R : Valid_Big_Integer) return Boolean :=
          "<="'Access;
      Val          : Value_Type;
   begin
      if Present (Iterator_Filter (Param_Spec)) then
         RAC_Unsupported
           ("Iterate_Loop_Param_Spec iterator filter", Param_Spec);
      end if;
      if not Is_Discrete_Type (Iter_Typ) then
         RAC_Unsupported
           ("Iterate_Lop_Param_Spec not discrete type", Param_Spec);
      end if;

      Curr := Value_Enum_Integer (Low);
      Stop := Value_Enum_Integer (High);

      if Reverse_Present (Param_Spec) then
         --  Reverse the loop direction
         declare
            Tmp : constant Big_Integer := Curr;
         begin
            Curr := Stop;
            Stop := Tmp;
         end;
         Step := To_Big_Integer (-1);
         Test := ">="'Access;
      end if;

      RAC_Trace ("Loop from " & To_String (Curr) & " to "
                 & To_String (Stop) & " by " & To_String (Step));
      begin
         while Test (Curr, Stop) loop
            Check_Fuel_Decrease (Ctx.Fuel);

            RAC_Trace ("Iterate : " & To_String (Curr));
            if Is_Integer_Type (Iter_Typ) then
               Val := Integer_Value (Curr, Iter_Typ, Empty);
            elsif Is_Enumeration_Type (Iter_Typ) then
               Val := Enum_Value (UI_From_String (To_String (Curr)), Iter_Typ);
            end if;
            Set_Value (Ctx.Env (Ctx.Env.First), Id, new Value_Type'(Val));
            Iteration.all;
            Curr := Curr + Step;
         end loop;
         Ctx.Env (Ctx.Env.First).Bindings.Exclude (Id);
      exception
         when Exn_RAC_Exit =>
            Ctx.Env (Ctx.Env.First).Bindings.Exclude (Id);

         --  Do not remove the loop parameter from the context in case of RAC
         --  failure, as the value will be needed for counterexample display,
         --  in case this RAC was triggered by fuzzing.
         when Exn_RAC_Failure =>
            raise;

         --  The call to Iteration will raise local exception Break to return
         --  early from the iteration.
         when others =>
            Ctx.Env (Ctx.Env.First).Bindings.Exclude (Id);
            raise;
      end;
   end Iterate_Loop_Param_Spec;

   -----------------------
   -- Match_Alternative --
   -----------------------

   function Match_Alternative
     (V  : Value_Type;
      Ch : Node_Id) return Boolean
   is

      function Check_Range
        (Range_Node : Node_Id;
         Expr       : Value_Type) return Boolean;
      --  Check if Expr falls into the range described by Range_Node

      function Check_Subtype
        (Def_Id : Type_Kind_Id;
         Expr   : Value_Type) return Boolean;
      --  Check if Expr matches with the possible values of the type when they
      --  are described by a static predicate or by a range.

      -----------------
      -- Check_Range --
      -----------------

      function Check_Range
        (Range_Node : Node_Id;
         Expr       : Value_Type) return Boolean
      is
         Low        : constant Big_Integer :=
           Value_Enum_Integer (RAC_Expr (Low_Bound (Range_Node)));
         High       : constant Big_Integer :=
           Value_Enum_Integer (RAC_Expr (High_Bound (Range_Node)));
         Expr_Value : constant Big_Integer := Value_Enum_Integer (Expr);
      begin
         return In_Range (Expr_Value, Low, High);
      end Check_Range;

      -------------------
      -- Check_Subtype --
      -------------------

      function Check_Subtype
        (Def_Id : Type_Kind_Id;
         Expr   : Value_Type) return Boolean
      is
         Option : Node_Id;
         Match  : Boolean := False;
      begin
         --  Subtype with static predicate
         if Has_Predicates (Def_Id) and then Has_Static_Predicate (Def_Id)
         then
            Option := First (Static_Discrete_Predicate (Def_Id));

            while not Match and then Present (Option) loop
               if Nkind (Option) = N_Range then
                  Match := Check_Range (Get_Range (Option), Expr);
               else
                  Match := Value_Enum_Integer (Expr) =
                    Value_Enum_Integer (RAC_Expr (Option));
               end if;

               Next (Option);
            end loop;

         --  Other subtypes
         else
            Match := Check_Range (Get_Range (Def_Id), Expr);
         end if;

         return Match;
      end Check_Subtype;

   begin
      --  Others
      if Nkind (Ch) = N_Others_Choice then
         return True;

      --  Subtypes
      elsif Is_Entity_Name (Ch) and then Is_Type (Entity (Ch)) then
         return Check_Subtype (Retysp (Entity (Ch)), V);

      --  Ranges
      elsif Nkind (Ch) = N_Range then
         return Check_Range (Get_Range (Ch), V);

      --  Other expressions
      else
         return V = RAC_Expr (Ch);
      end if;

   end Match_Alternative;

   ----------------------------
   -- Match_Case_Alternative --
   ----------------------------

   procedure Match_Case_Alternative (N : Node_Id; A : out Node_Id) is
      V  : constant Value_Type := RAC_Expr (Expression (N));
      Ch : Node_Id;
   begin
      A := First_Non_Pragma (Alternatives (N));

      while Present (A) loop
         Ch := First (Discrete_Choices (A));

         while Present (Ch) loop

            if Match_Alternative (V, Ch) then
               return;
            end if;

            Next (Ch);
         end loop;
         Next_Non_Pragma (A);
      end loop;

   end Match_Case_Alternative;

   -----------------
   -- Param_Scope --
   -----------------

   function Param_Scope (Call : Node_Id) return Scopes is
      Res : Scopes;

      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id);
      --  Add a parameter to Res

      -------------------
      -- Process_Param --
      -------------------

      procedure Process_Param (Formal : Entity_Id; Actual : Node_Id) is
         Val : Value_Access;
      begin

         --  if Is_Scalar_Type (Etype (Par)) then
         --    -> pass by value; copy out parameters after return
         --       (see Copy_Out_Parameters)
         --  elsif Ekind (Par) in E_In_Out_Parameter | E_Out_Parameter then
         --    -> pass by reference
         --  else -- Ekind (Par) = E_In_Parameter
         --    -> pass by copy
         --  end if

         --  ??? Due to SPARK anti-aliasing rules the copying of scalar values
         --      could be removed

         if Is_Scalar_Type (Etype (Actual)) then
            Val := new Value_Type'(Copy (RAC_Expr (Actual)));
         else
            case Formal_Kind (Ekind (Formal)) is
               when E_In_Parameter =>
                  Val := new Value_Type'(Copy (RAC_Expr (Actual)));
               when E_In_Out_Parameter | E_Out_Parameter =>
                  Val := RAC_Expr_LHS (Actual);
            end case;
         end if;

         if Is_Integer_Type (Etype (Formal)) then
            Check_Integer (Val.all, Etype (Formal), Actual);
         end if;

         Res.Bindings.Insert (Formal, Val);
      end Process_Param;

      procedure Iterate_Call is new Iterate_Call_Parameters (Process_Param);

   --  Start of processing for Param_Scope

   begin
      Iterate_Call (Call);
      return Res;
   end Param_Scope;

   -----------
   -- Slide --
   -----------

   procedure Slide
     (V : in out Value_Type;
      E :        Entity_Id)
   is
      New_Bounds : constant Node_Id := Get_Range (First_Index (E));
      New_First  : constant Big_Integer :=
        Value_Enum_Integer (RAC_Expr (Low_Bound (New_Bounds)));
      Offset     : constant Big_Integer := New_First - V.First_Attr.Content;

   begin
      if Offset /= 0 then
         declare
            use Big_Integer_To_Value_Maps;

            New_Values :          Map;
            Old_Values : constant Map := V.Array_Values;
            New_Last   : constant Big_Integer :=
              Value_Enum_Integer (RAC_Expr (High_Bound (New_Bounds)));
         begin
            for C in Old_Values.Iterate loop
               New_Values.Insert (Key (C) + Offset, Element (C));
            end loop;

            V.First_Attr   := (True, New_First);
            V.Last_Attr    := (True, New_Last);
            V.Array_Values := New_Values;
         end;
      end if;
   end Slide;

   -------------------------
   -- Peek_Exn_RAC_Result --
   -------------------------

   function Peek_Exn_RAC_Result return Result is
   begin
      if not Exn_RAC_Result.Present then
         raise Program_Error with "Peek_Exn_RAC_Result";
      end if;

      return Exn_RAC_Result.Content;
   end Peek_Exn_RAC_Result;

   --------------
   -- RAC_Call --
   --------------

   function RAC_Call
     (N            : Node_Id;
      E            : Entity_Id;
      Is_Main      : Boolean := False;
      Fuzz_Formals : Boolean := False)
      return Opt_Value_Type
   is
      function Cntexmp_Param_Scope return Scopes;
      --  Create a scope of parameters from the counterexample

      procedure Rem_Stack_Height_Push;

      procedure Rem_Stack_Height_Pop;

      -------------------------
      -- Initial_Param_Scope --
      -------------------------

      function Cntexmp_Param_Scope return Scopes is
         Res    : Scopes;
         Param  : Entity_Id  := First_Formal (E);
         Is_Out : Boolean;
         V      : Value_Type;
         Origin : Value_Origin;
      begin
         while Present (Param) loop
            Is_Out := Ekind (Param) = E_Out_Parameter;
            V := Get_Value (Param, Empty, Is_Out, Fuzz_Formals, Origin);
            Res.Bindings.Insert (Param, new Value_Type'(V));
            RAC_Trace ("Initialize parameter "
                       & Get_Name_String (Chars (Param)) & " to "
                       & To_String (V) & " " & Value_Origin'Image (Origin));
            Next_Formal (Param);
         end loop;
         return Res;
      end Cntexmp_Param_Scope;

      -------------------------------
      -- Rem_Stack_Height_Decrease --
      -------------------------------

      procedure Rem_Stack_Height_Push is
      begin
         if Ctx.Rem_Stack_Height > 0 then
            Ctx.Rem_Stack_Height := Ctx.Rem_Stack_Height - 1;
         end if;
         if Ctx.Rem_Stack_Height = 0 then
            RAC_Incomplete ("Stack overflow");
         end if;
      end Rem_Stack_Height_Push;

      -------------------------------
      -- Rem_Stack_Height_Increase --
      -------------------------------

      procedure Rem_Stack_Height_Pop is
      begin
         if Ctx.Rem_Stack_Height > 0 then
            Ctx.Rem_Stack_Height := Ctx.Rem_Stack_Height + 1;
         end if;
      end Rem_Stack_Height_Pop;

      --  Local variables

      Pres      : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Precondition);
      Posts     : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Postcondition);
      Bodie     : constant Node_Id := Get_Body (E);
      Old_Nodes : Node_Sets.Set;
      Res       : Opt_Value_Type;
      Sc        : Scopes;

   --  Start of processing for RAC_Call

   begin
      RAC_Trace ("call " & Get_Name_String (Chars (E)));
      Rem_Stack_Height_Push;

      if Is_Main then
         Sc := Cntexmp_Param_Scope;
      elsif Present (N) then
         Sc := Param_Scope (N);
      end if;

      begin
         Res := RAC_Call_Builtin (E, Sc, Ctx.Do_Sideeffects);
         Rem_Stack_Height_Pop;
         return Res;
      exception
         when No_Builtin =>
            null;
      end;

      if Present (Get_Pragma (E, Pragma_Contract_Cases)) then
         RAC_Unsupported ("RAC_Call pragma contract cases",
                          Get_Pragma (E, Pragma_Contract_Cases));
      end if;

      Ctx.Env.Prepend (Sc);

      --  Store value of the 'Old prefixes
      Collect_Attr_Parts (Posts, Snames.Name_Old, Old_Nodes);
      Evaluate_Attribute_Prefix_Values (Snames.Name_Old, Old_Nodes);

      --  Check preconditions and get stuck in main functions
      begin
         Check_List (Pres, "Precondition", VC_Precondition);
      exception
         when Exn_RAC_Failure =>
            if
              Is_Main and then
              Peek_Exn_RAC_Result.Res_VC_Kind = VC_Precondition
            then
               declare
                  R : constant Result := Flush_Exn_RAC_Result;
               begin
                  RAC_Stuck ("precondition of main function violated (" &
                               VC_Kind'Image (R.Res_VC_Kind) & " )");
               end;
            elsif Peek_Exn_RAC_Result.Res_VC_Kind = VC_Precondition
              and then Present (N)
            then
               RAC_Failure (N, Flush_Exn_RAC_Result.Res_VC_Kind);
            else
               raise;
            end if;
      end;

      --  We do not execute the call if there is no body for E or if the body
      --  is not in SPARK.

      if No (Bodie) then
         RAC_Incomplete
           ("No body for subprogram " & Get_Name_String (Chars (E)));
      elsif not SPARK_Definition.Entity_Body_In_SPARK (E) then
         RAC_Incomplete
           ("Body for subprogram " & Get_Name_String (Chars (E))
            & " is not in SPARK");
      end if;

      RAC_Decls (Declarations (Bodie));

      --  Execute subprogram body
      begin
         RAC_Node (Handled_Statement_Sequence (Bodie));
         RAC_Trace ("call terminated");
         Res := No_Value;
      exception
         when Exn_RAC_Return =>
            RAC_Trace ("call return");
            Res := Flush_RAC_Return;
      end;

      --  Add result attribute for checking the postcondition
      if Res.Present then
         Ctx.Env (Ctx.Env.First).Bindings.Insert
           (E, new Value_Type'(Res.Content));
      end if;

      Check_List (Posts, "Postcondition", VC_Postcondition);

      --  Cleanup
      if Res.Present then
         Ctx.Env (Ctx.Env.First).Bindings.Delete (E);
      end if;

      Sc := Ctx.Env (Ctx.Env.First);
      Ctx.Env.Delete_First;
      if not Is_Main and then Present (N) then
         Copy_Out_Parameters (N, Sc);
      end if;

      RAC_Trace ("call result of " & Get_Name_String (Chars (E)) &
                   ": " & To_String (Res));
      Rem_Stack_Height_Pop;
      return Res;
   end RAC_Call;

   ----------------------
   -- RAC_Call_Builtin --
   ----------------------

   function RAC_Call_Builtin
     (E              : Entity_Id;
      Sc             : Scopes;
      Do_Sideeffects : Boolean)
      return Opt_Value_Type is
   begin
      --  The implementation of Ada.Text_IO.Put_Line is just added for running
      --  the added tests TC02-027__RAC and comparing the execution with the
      --  compiled program based on the output.

      if Is_Unary_Text_IO_Put_Line (E) then
         if Do_Sideeffects then
            declare
               Val     : Value_Access renames
                 Sc.Bindings (Sc.Bindings.First);
               Fst     : constant Big_Integer := Val.First_Attr.Content;
               Lst     : constant Big_Integer := Val.Last_Attr.Content;
               S       : String (To_Integer (Fst) .. To_Integer (Lst));
               Default : constant Character :=
                 Value_Character (Val.Array_Others.all);
            begin
               if Lst - Fst > 10_000
               then
                  RAC_Incomplete ("String too long");
               --  ??? Next test should not be needed, as counterexample value
               --  should already be valid in its type due to prior filtering.
               elsif Fst <= Lst and then Fst <= 0 then
                  RAC_Stuck
                    ("Non-empty string starting at non-positive index");
               else
                  for K in S'Range loop
                     if Val.Array_Values.Contains (To_Big_Integer (K)) then
                        S (K) := Value_Character
                          (Val.Array_Values (To_Big_Integer (K)).all);
                     else
                        S (K) := Default;
                     end if;
                  end loop;

                  Put_Line (S);
               end if;
            end;
         end if;
         return No_Value;
      else
         raise No_Builtin;
      end if;
   end RAC_Call_Builtin;

   --------------
   -- RAC_Decl --
   --------------

   procedure RAC_Decl (Decl : Node_Id) is
   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>
            declare
               V  : Value_Type;
               Ty : Entity_Id :=
                 Retysp (Etype (Unique_Defining_Entity (Decl)));
            begin
               if Present (Expression (Decl)) then
                  V := RAC_Expr (Expression (Decl));

                  if V.K = Array_K and then Is_Constrained (Ty) then
                        Slide (V, Ty);
                  end if;
               else
                  Ty := Retysp (Ty);
                  Check_Supported_Type (Ty);
                  --  ??? Don't check range of integer values

                  V := Default_Value (Ty, Check => False);
               end if;

               Set_Value
                 (Ctx.Env (Ctx.Env.First),
                  Defining_Identifier (Decl),
                  new Value_Type'(V));
            end;

         when N_Package_Declaration =>
            declare
               Unique_E : constant Entity_Id :=
                 Unique_Defining_Entity (Decl);
            begin
               RAC_Decls (Visible_Declarations_Of_Package (Unique_E));
               RAC_Decls (Private_Declarations_Of_Package (Unique_E));
            end;

         when N_Package_Body =>
            if not Is_Generic_Unit (Unique_Defining_Entity (Decl)) then
               RAC_Decls (Declarations (Decl));
               RAC_Node (Handled_Statement_Sequence (Decl));
            end if;

         when N_Defining_Identifier =>
            case Ekind (Decl) is
               when E_Package =>
                     RAC_Decls (Visible_Declarations_Of_Package (Decl));
                     RAC_Decls (Private_Declarations_Of_Package (Decl));

               when E_Package_Body =>
                  if not Is_Generic_Unit (Decl) then
                     RAC_Decls (Declarations (Decl));
                     RAC_Node (Handled_Statement_Sequence (Decl));
                  end if;

               when others =>
                  RAC_Unsupported
                    ("RAC_Decl",
                     "N_Defining_Identifier not package or package body");
            end case;

         when N_Pragma
            | N_Full_Type_Declaration
            | N_Subtype_Declaration
            | N_Subprogram_Declaration
            | N_Subprogram_Body
            | N_Ignored_In_SPARK
         =>
            null;

         when others =>
            RAC_Unsupported ("RAC_Decl", Node_Kind'Image (Nkind (Decl)));
      end case;
   end RAC_Decl;

   ---------------
   -- RAC_Decls --
   ---------------

   procedure RAC_Decls (Decls : List_Id) is
      Decl : Node_Id := First (Decls);
   begin
      while Present (Decl) loop
         RAC_Decl (Decl);
         Next (Decl);
      end loop;
   end RAC_Decls;

   -----------------
   -- RAC_Execute --
   -----------------

   function RAC_Execute
     (E              : Entity_Id;
      Cntexmp        : Cntexample_File_Maps.Map := Cntexample_File_Maps.Empty;
      Do_Sideeffects : Boolean := False;
      Fuel           : Fuel_Access := null;
      Stack_Height   : Integer := -1;
      Use_Fuzzing    : Boolean := False)
      return Result
   is
      function Empty_Global_Env return Environments.Vector;
      --  Create an initial environment with only an empty global scope

      procedure Init_Global_Scope;
      --  Initializes the global scope (Ctx.Env (Ctx.Env.First)) with global
      --  variables with values from Get_Value. The global scope is initialized
      --  with fuzzed values if Use_Fuzzing is set to True.

      ----------------------
      -- Empty_Global_Env --
      ----------------------

      function Empty_Global_Env return Environments.Vector
      is
         Env : Environments.Vector := Environments.Empty;
      begin
         Env.Append (Scopes'(others => <>));
         return Env;
      end Empty_Global_Env;

      -----------------------
      -- Init_Global_Scope --
      -----------------------

      procedure Init_Global_Scope is
         Reads, Writes : Flow_Id_Sets.Set;
         Use_Expr      : Boolean;
         B             : Value_Access;
         Scope         : constant Flow_Scope := Get_Flow_Scope (E);
      begin
         Get_Proof_Globals (E, Reads, Writes, False, Scope);

         for Id of Reads loop
            if Id.Kind = Direct_Mapping then
               Use_Expr := Ekind (Id.Node) = E_Constant;
               Init_Global (Id.Node, Use_Expr, Use_Fuzzing, False, B, "read");
            end if;
         end loop;

         for Id of Writes loop
            if Id.Kind = Direct_Mapping
              and then not Reads.Contains (Id)
            then
               Init_Global (Id.Node, False, False, True, B, "write");
            end if;
         end loop;
      end Init_Global_Scope;

   --  Start of processing for RAC_Execute

   begin
      Ctx :=
        (Env              => Empty_Global_Env,
         Cntexmp          => Cntexmp,
         Fuel             => Fuel,
         Rem_Stack_Height => Stack_Height,
         Do_Sideeffects   => Do_Sideeffects);

      RAC_Trace ("cntexmp: " & Write (To_JSON (Cntexmp), False));
      RAC_Trace ("entry: " & Full_Name (E));

      case Ekind (E) is
         when E_Function
            | E_Procedure
            =>
            Init_Global_Scope;
            return
              (Res_Kind  => Res_Normal,
               Res_Value =>
                  RAC_Call
                 (Empty, E, Is_Main => True, Fuzz_Formals => Use_Fuzzing));

         when E_Package
            | E_Package_Body
            =>
               RAC_Decl (E);

               return (Res_Kind  => Res_Normal,
                       Res_Value => (Present => False));

         when E_Task_Type
            | E_Entry
            | E_Private_Type
            | E_Protected_Type
         =>
            RAC_Unsupported ("RAC_Execute", E);
         when others =>
            raise Program_Error with
              ("Cannot execute RAC entity " & Entity_Kind'Image (Ekind (E)));
      end case;

   exception
      when Exn_RAC_Failure | Exn_RAC_Stuck | Exn_RAC_Incomplete =>
         return Flush_Exn_RAC_Result;
   end RAC_Execute;

   --------------
   -- RAC_Expr --
   --------------

   function RAC_Expr
     (N : N_Subexpr_Id; Ty0 : Entity_Id := Empty) return Value_Type
   is
      Ty : constant Entity_Id :=
        (if Present (Ty0) then Retysp (Ty0) else Retysp (Etype (N)));

      function RAC_Aggregate return Value_Type;

      function RAC_Attribute_Reference return Value_Type;

      function RAC_Binary_Op return Value_Type;

      function RAC_If_Expression return Value_Type;

      function RAC_In (Negate : Boolean := False) return Value_Type;

      function RAC_Op_Compare (Left, Right : Value_Type) return Boolean;

      function RAC_Unary_Op return Value_Type;

      -------------------
      -- RAC_Aggregate --
      -------------------

      function RAC_Aggregate return Value_Type is
         --  ([E with delta] Ch, ... => V, ...)

         procedure Iterated_Component
           (Iterated_Assoc   :     Node_Id;
            Component_Values : out Big_Integer_To_Value_Maps.Map);
         --  Set the iterated array components' values. Opens a new scope for
         --  the iteration variable, bind it and update its value throughout
         --  the execution in case the expression depends on it. Remove the
         --  scope upon exit.

         ------------------------
         -- Iterated_Component --
         ------------------------

         procedure Iterated_Component
           (Iterated_Assoc   :     Node_Id;
            Component_Values : out Big_Integer_To_Value_Maps.Map)
         is
            Choice :          Node_Id :=
              First (Discrete_Choices (Iterated_Assoc));
            Def_Id : constant Node_Id := Defining_Identifier (Iterated_Assoc);
            Expr   : constant Node_Id := Expression (Iterated_Assoc);
         begin
            --  Add a new scope for the for loop in order to store the
            --  iteration variable.

            Ctx.Env.Prepend (Scopes'(others => <>));

            while Present (Choice) loop
               Check_Fuel_Decrease (Ctx.Fuel);

               if Nkind (Choice) in N_Range | N_Subtype_Indication
                 or else (Is_Entity_Name (Choice)
                          and then Is_Type (Entity (Choice)))
               then
                  declare
                     Choice_Range : constant Node_Id     := Get_Range (Choice);
                     Curr         :          Big_Integer :=
                       Value_Enum_Integer
                         (RAC_Expr (Low_Bound (Choice_Range)));
                     High         : constant Big_Integer :=
                       Value_Enum_Integer
                         (RAC_Expr (High_Bound (Choice_Range)));
                     Iter_Param   :          Value_Type;
                  begin
                     while Curr <= High loop
                        Check_Fuel_Decrease (Ctx.Fuel);

                        Iter_Param := Int_Value (Curr, Etype (Def_Id));

                        Set_Value (Ctx.Env (Ctx.Env.First),
                                   Def_Id,
                                   new Value_Type'(Iter_Param));

                        Component_Values.Include
                          (Curr, new Value_Type'(RAC_Expr (Expr)));

                        Curr := Curr + 1;
                     end loop;
                  end;

               else
                  declare
                     Choice_Val : constant Value_Type := RAC_Expr (Choice);
                  begin
                     Set_Value (Ctx.Env (Ctx.Env.First),
                                Def_Id,
                                new Value_Type'(Choice_Val));

                     Component_Values.Include
                       (Value_Enum_Integer (Choice_Val),
                        new Value_Type'(RAC_Expr (Expr)));
                  end;
               end if;
               Next (Choice);
            end loop;

            Ctx.Env.Delete_First;
         end Iterated_Component;

         --  Local variables

         Assoc  : Node_Id := First (Component_Associations (N));
         Choice : Node_Id;
         Res    : Value_Type;
         Val    : Value_Access;

      begin

         if Nkind (N) = N_Delta_Aggregate then
            Res := RAC_Expr (Expression (N));
            Res.AST_Ty := Etype (N);
         else
            if Is_Record_Type (Ty) then
               Res := Record_Value (Entity_To_Value_Maps.Empty, Ty);
            else
               pragma Assert (Is_Array_Type (Ty));
               declare
                  First, Last : Big_Integer;
               begin
                  Get_Bounds (Aggregate_Bounds (N), First, Last);
                  Res := Array_Value
                    (First, Last, Big_Integer_To_Value_Maps.Empty, null, Ty);
               end;
            end if;
         end if;

         if Is_Record_Type (Ty) then

            declare
               Root_Ty : constant Type_Kind_Id := Root_Retysp (Ty);
            begin
               if Ty /= Root_Ty and then Is_Tagged_Type (Root_Ty) then
                  RAC_Unsupported ("RAC_Expr aggregate record",
                                   "tagged types extension");
               end if;
            end;

            while Present (Assoc) loop
               Check_Fuel_Decrease (Ctx.Fuel);

               Val := new Value_Type'(RAC_Expr (Expression (Assoc)));
               Choice := First (Choice_List (Assoc));

               while Present (Choice) loop
                  Check_Fuel_Decrease (Ctx.Fuel);

                  declare
                     Component : constant Entity_Id :=
                       Search_Component_In_Type (Ty, Entity (Choice));
                  begin
                     pragma Assert (Present (Component));
                     Res.Record_Fields.Include (Component, Val);
                  end;
                  Next (Choice);
               end loop;
               Next (Assoc);
            end loop;

         else
            pragma Assert (Is_Array_Type (Ty));

            --  Positional components

            if Nkind (N) = N_Aggregate and then Present (Expressions (N)) then
               declare
                  Expr : Node_Id     := First (Expressions (N));
                  Curr : Big_Integer := Value_Enum_Integer
                    (RAC_Expr (Low_Bound (Aggregate_Bounds (N))));
               begin
                  while Present (Expr) loop
                     Check_Fuel_Decrease (Ctx.Fuel);

                     Res.Array_Values.Include (Curr,
                                               new Value_Type'
                                                 (RAC_Expr (Expr)));
                     Next (Expr);
                     Curr := Curr + 1;
                  end loop;
               end;
            end if;

            --  Named components

            if Present (Component_Associations (N)) then

               while Present (Assoc) loop
                  Check_Fuel_Decrease (Ctx.Fuel);

                  Choice := First (Choice_List (Assoc));

                  while Present (Choice) loop
                     Check_Fuel_Decrease (Ctx.Fuel);

                     --  When the elements' values are attributed using a loop,
                     --  iterate over it to retrieve the value of each
                     --  individual element. Then, add the values to the actual
                     --  array.

                     if Nkind (Assoc) = N_Iterated_Component_Association
                       and then Present (Defining_Identifier (Assoc))
                     then
                        declare
                           Iter_Comp_Values : Big_Integer_To_Value_Maps.Map;
                        begin
                           Iterated_Component (Assoc, Iter_Comp_Values);

                           for Component in Iter_Comp_Values.Iterate loop
                              Res.Array_Values.Include
                                (Big_Integer_To_Value_Maps.Key (Component),
                                 Big_Integer_To_Value_Maps.Element
                                   (Component));
                           end loop;
                        end;

                     else
                        Val := new Value_Type'
                          (if Box_Present (Assoc)
                           then (if Has_Default_Aspect (Ty)
                                 then RAC_Expr
                                   (Default_Aspect_Component_Value (Ty))
                                 else
                                    Default_Value (Component_Type (Ty)))
                           else RAC_Expr (Expression (Assoc)));

                        if Nkind (Choice) in N_Range | N_Subtype_Indication
                          or else (Is_Entity_Name (Choice)
                                   and then Is_Type (Entity (Choice)))
                        then
                           declare
                              Choice_Range : constant Node_Id :=
                                Get_Range (Choice);
                              Curr         :          Big_Integer :=
                                Value_Enum_Integer
                                  (RAC_Expr (Low_Bound (Choice_Range)));
                              High         : constant Big_Integer :=
                                Value_Enum_Integer
                                  (RAC_Expr (High_Bound (Choice_Range)));
                           begin
                              while Curr <= High loop
                                 Check_Fuel_Decrease (Ctx.Fuel);

                                 Res.Array_Values.Include (Curr, Val);
                                 Curr := Curr + 1;
                              end loop;
                           end;

                        else
                           case Nkind (Choice) is
                           when N_Subexpr =>
                              Res.Array_Values.Include
                                (Value_Enum_Integer (RAC_Expr (Choice)), Val);

                           when N_Others_Choice =>
                              Res.Array_Others := Val;

                           when others =>
                              raise Program_Error;

                           end case;
                        end if;
                     end if;
                     Next (Choice);
                  end loop;
                  Next (Assoc);
               end loop;
            end if;
         end if;

         Cleanup_Counterexample_Value (Res, N);
         return Res;
      end RAC_Aggregate;

      -----------------------------
      -- RAC_Attribute_Reference --
      -----------------------------

      function RAC_Attribute_Reference return Value_Type is
      begin
         case Attribute_Name (N) is
            when Snames.Name_Old =>
               --  E'Old
               declare
                  P : constant Node_Id := Prefix (N);
               begin
                  return Ctx.Env (Ctx.Env.First).Old_Attrs (P);
               end;

            --  For each expression P'Loop_Entry, the value of the prefix P has
            --  been stored in the scope for the corresponding loop. This might
            --  not be the first scope of the environment, in case of local
            --  declare blocks inside the loop.

            when Snames.Name_Loop_Entry =>
               declare
                  P : constant Node_Id := Prefix (N);
               begin
                  for Scop of Ctx.Env loop
                     if Scop.Loop_Entry_Attrs.Contains (P) then
                        return Scop.Loop_Entry_Attrs (P);
                     end if;
                  end loop;
                  raise Program_Error;
               end;

            when Snames.Name_Result =>
               --  E'Result
               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
               begin
                  return Find_Binding (E).all;
               end;

            when Snames.Name_First
               | Snames.Name_Last
            =>
               if Is_Array_Type (Etype (Prefix (N))) then
                  declare
                     Index_Ty : constant Entity_Id :=
                       Etype (First_Index (Etype (Prefix (N))));
                     V : constant Value_Type := RAC_Expr (Prefix (N));
                  begin
                     case V.K is
                        when Array_K =>
                           if Attribute_Name (N) = Snames.Name_First then
                              return Int_Value
                                (V.First_Attr.Content, Index_Ty);
                           else
                              return Int_Value
                                (V.Last_Attr.Content, Index_Ty);
                           end if;
                        when others =>
                           raise Program_Error;
                     end case;
                  end;

               --  T'First, T'Last
               --  ??? Do we get such static values which are not folded by the
               --  frontend, for a constrained integer type?
               elsif not Is_Integer_Type (Etype (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference first/last not integer", N);
               end if;

               declare
                  Fst, Lst : Big_Integer;
               begin
                  Get_Integer_Type_Bounds (Etype (N), Fst, Lst);

                  case Attribute_Name (N) is
                  when Snames.Name_First =>
                     return Int_Value (Fst, Etype (N));
                  when Snames.Name_Last =>
                     return Int_Value (Lst, Etype (N));
                  when others =>
                     raise Program_Error;
                  end case;
               end;

            when Snames.Name_Min
               | Snames.Name_Max
            =>
               --  T'Min (Ex, Ex2), T'Max (Ex, Ex2)
               if not (Is_Integer_Type (Etype (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference min/max not integer", N);
               end if;

               declare
                  Ex : constant Node_Id := First (Expressions (N));
                  I1 : constant Big_Integer :=
                    Value_Enum_Integer (RAC_Expr (Ex));
                  I2 : constant Big_Integer :=
                    Value_Enum_Integer (RAC_Expr (Next (Ex)));
               begin
                  case Attribute_Name (N) is
                     when Snames.Name_Min =>
                        return Integer_Value (Min (I1, I2), N);
                     when Snames.Name_Max =>
                        return Integer_Value (Max (I1, I2), N);
                     when others =>
                        raise Program_Error;
                  end case;
               end;

            when Snames.Name_Succ
               | Snames.Name_Prev
            =>
               --  T'Succ (Ex), T'Prev (Ex)
               if not (Is_Enumeration_Type (Etype (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference succ/prev not enum", N);
               end if;

               declare
                  Ex  : constant Node_Id := First (Expressions (N));
                  E   : constant Entity_Id :=
                    RAC_Expr (Ex).Scalar_Content.Enum_Entity;
                  Ty  : constant Entity_Id := Etype (N);
                  Res : Entity_Id := Empty; -- the resulting enum literal
               begin
                  case Attribute_Name (N) is
                     when Snames.Name_Succ =>
                        Res := Next_Literal (E);
                     when Snames.Name_Prev =>
                        declare
                           Next : Entity_Id := First_Literal (Ty);
                        begin
                           while Next /= E loop
                              Res := Next;
                              Next := Next_Literal (Next);
                           end loop;
                        end;
                     when others =>
                        raise Program_Error;
                  end case;

                  if No (Res) then
                     RAC_Failure (Ex, VC_Range_Check);
                  end if;

                  return Enum_Value (Res, Etype (N));
               end;

            when Snames.Name_Update =>
               --  Ex'Update ((Ch | ... => V, ...), ...)
               declare
                  F                : Entity_To_Value_Maps.Map;
                  Ex, As, Ch       : Node_Id;
                  V                : Value_Type;
                  FC               : Entity_To_Value_Maps.Cursor;
                  Record_Not_Array : constant Boolean := Is_Record_Type (Ty);
                  Prefix_Value     : constant Value_Type :=
                                       RAC_Expr (Prefix (N));
                  Comp             : Entity_Id;
               begin
                  pragma Assert (Record_Not_Array xor Is_Array_Type (Ty));
                  if Record_Not_Array then
                     F := Copy (Prefix_Value.Record_Fields);
                     Ex := First (Expressions (N));

                     while Present (Ex) loop
                        As := First (Component_Associations (Ex));
                        while Present (As) loop
                           V := RAC_Expr (Expression (As));
                           Ch := First (Choice_List (As));

                           if Nkind (Ch) /= N_Identifier then
                              RAC_Unsupported
                                ("RAC_Attribute_Reference update", Ch);
                           end if;

                           while Present (Ch) loop
                              Comp := Search_Component_In_Type
                                (Prefix_Value.AST_Ty, Entity (Ch));
                              FC := F.Find (Comp);

                              if not Entity_To_Value_Maps.Has_Element (FC) then
                                 pragma Assert
                                   (Has_Discriminants (Prefix_Value.AST_Ty));
                                 RAC_Failure (Ch, VC_Discriminant_Check);
                              end if;

                              F.Replace_Element (FC, new Value_Type'(V));
                              Next (Ch);
                           end loop;
                           Next (As);
                        end loop;
                        Next (Ex);
                     end loop;

                     return Record_Value (F, Ty);
                  else
                     RAC_Unsupported
                       ("RAC_Attribute_Reference", "update array");
                  end if;
               end;

            when Snames.Name_Image =>
               if Is_Empty_List (Expressions (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference 'Image without argument", N);
               end if;
               return String_Value
                 (To_String (RAC_Expr (First (Expressions (N)))));

            when Snames.Name_Length =>
               if not Is_Empty_List (Expressions (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference 'Length with argument", N);
               elsif Etype (Prefix (N)) = Entity (Prefix (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference 'Length on type", N);
               end if;

               declare
                  V : constant Value_Type := RAC_Expr (Prefix (N));
               begin
                  if Is_Array_Type (Etype (Prefix (N))) then
                     case V.K is
                        when Array_K =>
                           return Int_Value
                             (Max (0, 1 + V.Last_Attr.Content
                                        - V.First_Attr.Content), Etype (N));
                        when others =>
                           raise Program_Error;
                     end case;
                  else
                     RAC_Unsupported
                       ("RAC_Attribute_Reference 'Length prefix not string "
                          & "not array", N);
                  end if;
               end;

            when others =>
               RAC_Unsupported
                 ("RAC_Attribute_Reference",
                  Get_Name_String (Attribute_Name (N)));
         end case;
      end RAC_Attribute_Reference;

      -------------------
      -- RAC_Binary_Op --
      -------------------

      function RAC_Binary_Op return Value_Type is
         Left  : constant Value_Type := RAC_Expr (Left_Opnd (N));
         Right : constant Value_Type := RAC_Expr (Right_Opnd (N));
      begin
         case Nkind (N) is
            when N_Op_Add =>
               return
                 Integer_Value
                   (Value_Integer (Left) + Value_Integer (Right), N);

            when N_Op_Expon =>
               declare
                  Val_Left  : constant Big_Integer := Value_Integer (Left);
                  Val_Right : constant Big_Integer := Value_Integer (Right);

                  Real_Left : constant Long_Float :=
                    To_Long_Float (abs (Val_Left));
                  Int_Right : constant Integer := To_Integer (abs (Val_Right));
               begin
                  --  Protect against very large values which exceed what the
                  --  Big_Integers library can handle. We limit ourselves to
                  --  2**256 as GNAT currently supports up to 128-bits integers
                  --  (even if modular types would support larger values).
                  if Real_Left ** Int_Right >= 2.0 ** 256 then
                     RAC_Unsupported
                       ("RAC_Binary_Op too large exponentiation", N);
                  end if;

                  return Integer_Value
                    (Val_Left ** Natural (To_Integer (Val_Right)), N);
               end;

            when N_Op_Subtract =>
               return
                 Integer_Value
                   (Value_Integer (Left) - Value_Integer (Right), N);

            when N_Op_Divide .. N_Op_Rem =>
               if Nkind (N) in N_Op_Divide | N_Op_Mod | N_Op_Rem
                 and then Value_Integer (Right) = 0
               then
                  RAC_Failure (N, VC_Division_Check);
               end if;

               return
                 Integer_Value
                   ((case Nkind (N) is
                       when N_Op_Multiply =>
                          Value_Integer (Left) * Value_Integer (Right),
                       when N_Op_Divide   =>
                          Value_Integer (Left) / Value_Integer (Right),
                       when N_Op_Mod      =>
                          Value_Integer (Left) mod Value_Integer (Right),
                       when N_Op_Rem      =>
                          Value_Integer (Left) rem Value_Integer (Right),
                       when others        =>
                          raise Program_Error),
                    N);

            when N_Op_And .. N_Op_Xor =>
               if Is_Boolean_Type (Etype (N)) then
                  return
                    Boolean_Value
                      ((case Nkind (N) is
                          when N_Op_Or  =>
                            Value_Boolean (Left) or Value_Boolean (Right),
                          when N_Op_And =>
                            Value_Boolean (Left) and Value_Boolean (Right),
                          when N_Op_Xor =>
                            Value_Boolean (Left) xor Value_Boolean (Right),
                          when others   =>
                            RAC_Op_Compare (Left, Right)),
                       Etype (N));

               elsif Is_Modular_Integer_Type (Etype (N)) then
                  declare
                     L : constant Ulargest :=
                       Ulargest'Value (To_String (Value_Integer (Left)));
                     R : constant Ulargest :=
                       Ulargest'Value (To_String (Value_Integer (Right)));

                     function From_Ulargest (U : Ulargest) return Big_Integer
                     is (From_String (Ulargest'Image (U)));

                  begin
                     case Nkind (N) is
                        when N_Op_Or  =>
                           return Integer_Value (From_Ulargest (L or R), N);
                        when N_Op_And =>
                           return Integer_Value (From_Ulargest (L and R), N);
                        when N_Op_Xor =>
                           return Integer_Value (From_Ulargest (L xor R), N);
                        when others   =>
                           return
                             Boolean_Value
                               (RAC_Op_Compare (Left, Right), Etype (N));
                     end case;
                  end;

               else
                  RAC_Unsupported ("RAC_Binary_Op N_Op_Boolean", N);
               end if;

            when N_Op_Concat =>
               if Is_Constrained (Etype (N)) then
                  RAC_Unsupported
                    ("RAC_Binary_Op concat on constrained type", N);
               elsif Is_Component_Left_Opnd (N)
                 or else Is_Component_Right_Opnd (N)
               then
                  RAC_Unsupported
                    ("RAC_Binary_Op concat with a component operand", N);

               --  Concatenation of 2 arrays without sliding

               else
                  declare
                     R_Length : constant Big_Integer :=
                       Right.Last_Attr.Content - Right.First_Attr.Content + 1;
                     L_Length : constant Big_Integer :=
                       Left.Last_Attr.Content - Left.First_Attr.Content + 1;

                  begin
                     --  If Left or Right is empty, return the other

                     if L_Length <= 0 then
                        return Copy (Right);
                     elsif R_Length <= 0 then
                        return Copy (Left);

                     --  Otherwise, add the elements of Right into Left

                     elsif R_Length > 1000 then
                        RAC_Unsupported
                          ("RAC_Binary_Op concat with big right operand", N);
                     else
                        declare
                           Res     : Value_Type := Copy (Left);
                           R_First : Big_Integer renames
                             Right.First_Attr.Content;
                           L_Last  : Big_Integer renames
                             Left.Last_Attr.Content;
                           Val     : Value_Access;

                        begin
                           for K in 1 .. To_Integer (R_Length) loop
                              if Right.Array_Values.Contains
                                (R_First - 1 + To_Big_Integer (K))
                              then
                                 Val := Right.Array_Values
                                   (R_First - 1 + To_Big_Integer (K));
                              else
                                 Val := Right.Array_Others;
                              end if;

                              if Val /= null then
                                 Res.Array_Values.Insert
                                   (L_Last + To_Big_Integer (K),
                                    new Value_Type'(Copy (Val.all)));
                              end if;
                           end loop;

                           Res.Last_Attr.Content :=
                             Left.Last_Attr.Content + R_Length;
                           return Res;
                        end;
                     end if;
                  end;
               end if;

            when N_Op_Shift =>
               RAC_Unsupported ("RAC_Binary_Op", N);

            when others =>
               raise Program_Error;
         end case;
      end RAC_Binary_Op;

      -----------------------
      -- RAC_If_Expression --
      -----------------------

      function RAC_If_Expression return Value_Type is
         Cond_Expr : constant Node_Id := First (Expressions (N));
         Then_Expr : constant Node_Id := Next (Cond_Expr);
         Else_Expr : constant Node_Id := Next (Then_Expr);
      begin
         if Value_Boolean (RAC_Expr (Cond_Expr)) then
            return RAC_Expr (Then_Expr);
         else
            return RAC_Expr (Else_Expr);
         end if;
      end RAC_If_Expression;

      ------------
      -- RAC_In --
      ------------

      function RAC_In (Negate : Boolean := False) return Value_Type
      is
         procedure Get_Array_Bounds
           (Op_Node     :     Node_Id;
            Op_Ty       :     Type_Kind_Id;
            First, Last : out Big_Integer);
         --  Fill First and Last with the value of the bounds of the array
         --  type. If the array is not constrained, the node which has this
         --  array type is evaluated to get the bounds.

         procedure Get_Discriminant_Values
           (Op_Node      :     Node_Id;
            Op_Ty        :     Type_Kind_Id;
            Discr_Values : out Entity_To_Value_Maps.Map);
         --  Given a record, store each of its discriminants' values in a map

         function Match_Alternative_Non_Discrete
           (Left_Op  : Node_Id;
            Right_Op : Node_Id) return Boolean;
         --  Return true if Left_Op is a member of Right_Op

         ----------------------
         -- Get_Array_Bounds --
         ----------------------

         procedure Get_Array_Bounds
           (Op_Node     :     Node_Id;
            Op_Ty       :     Type_Kind_Id;
            First, Last : out Big_Integer)
         is
            Arr_Value :          Value_Type;
            First_Idx : constant Node_Id := First_Index (Op_Ty);
         begin
            if Is_Constrained (Op_Ty) then
               Get_Bounds (Get_Range (First_Idx), First, Last);
            else
               Arr_Value := RAC_Expr (Op_Node);
               First := Arr_Value.First_Attr.Content;
               Last  := Arr_Value.Last_Attr.Content;
            end if;
         end Get_Array_Bounds;

         -----------------------------
         -- Get_Discriminant_Values --
         -----------------------------

         procedure Get_Discriminant_Values
           (Op_Node      :     Node_Id;
            Op_Ty        :     Type_Kind_Id;
            Discr_Values : out Entity_To_Value_Maps.Map)
         is
            Discr       : Entity_Id;
            Elmt        : Elmt_Id;
            Rec_Value   : Value_Type;
            Discr_Value : Value_Access;
            Discr_Cur   : Entity_To_Value_Maps.Cursor;
         begin
            Discr := First_Discriminant (Root_Retysp (Op_Ty));

            if Is_Constrained (Op_Ty) then
               Elmt := First_Elmt (Discriminant_Constraint (Op_Ty));

               while Present (Discr) loop
                  Discr_Values.Insert
                    (Discr,
                     new Value_Type'(
                       RAC_Expr (Node (Elmt), Retysp (Etype (Discr)))));

                  Next_Discriminant (Discr);
                  Next_Elmt (Elmt);
               end loop;

            else
               Rec_Value := RAC_Expr (Op_Node);
               while Present (Discr) loop

                  Discr_Cur := Rec_Value.Record_Fields.Find (Discr);
                  Discr_Value := Entity_To_Value_Maps.Element (Discr_Cur);
                  Discr_Values.Insert (Discr,
                                       new Value_Type'(Discr_Value.all));

                  Next_Discriminant (Discr);
               end loop;

            end if;
         end Get_Discriminant_Values;

         ------------------------------------
         -- Match_Alternative_Non_Discrete --
         ------------------------------------

         function Match_Alternative_Non_Discrete
           (Left_Op  : Node_Id;
            Right_Op : Node_Id) return Boolean
         is
            Left_Ty      : constant Type_Kind_Id := Retysp (Etype (Left_Op));
            Right_Ty     : constant Type_Kind_Id := Retysp (Etype (Right_Op));
            Root_Left_Ty : constant Type_Kind_Id := Root_Retysp (Left_Ty);
            Match        : Boolean := False;
         begin
            --  Records
            if Is_Record_Type (Left_Ty) then

               if not Is_Constrained (Right_Ty)
                 or else Left_Ty = Right_Ty
                 or else Root_Left_Ty = Right_Ty
               then
                  return True;

               elsif Is_Tagged_Type (Left_Ty) then
                  RAC_Unsupported ("RAC_In tagged types", Left_Ty);

               elsif Has_Predicates (Right_Ty) then
                  RAC_Unsupported ("RAC_In type with predicate", Right_Ty);

               elsif Has_Discriminants (Left_Ty)
                 and then Is_Constrained (Right_Ty)
               then
                  declare
                     Left_Dis_Val  : Entity_To_Value_Maps.Map;
                     Right_Dis_Val : Entity_To_Value_Maps.Map;
                  begin
                     Get_Discriminant_Values
                       (Left_Op, Left_Ty, Left_Dis_Val);
                     Get_Discriminant_Values
                       (Right_Op, Right_Ty, Right_Dis_Val);

                     Match := Left_Dis_Val = Right_Dis_Val;
                  end;

               else
                  --  If there are no discriminants or if the type is not
                  --  constrained, the left and right operands necessarily
                  --  match.
                  Match := True;
               end if;

            --  Arrays
            elsif Is_Array_Type (Left_Ty) then
               if not Is_Constrained (Right_Ty)
                 or else Left_Ty = Right_Ty
                 or else Root_Left_Ty = Right_Ty
               then
                  return True;

               elsif Has_Predicates (Right_Ty) then
                  RAC_Unsupported ("RAC_In type with predicate", Right_Ty);

               else
                  declare
                     Left_First,  Left_Last  : Big_Integer;
                     Right_First, Right_Last : Big_Integer;
                  begin

                     Get_Array_Bounds
                       (Left_Op, Left_Ty, Left_First, Left_Last);
                     Get_Array_Bounds
                       (Right_Op, Right_Ty, Right_First, Right_Last);

                     Match := Left_First = Right_First
                       and then Left_Last = Right_Last;
                  end;
               end if;

            --  Floating and fixed point types
            elsif not Is_Discrete_Type (Etype (Left_Op)) then
               RAC_Unsupported ("RAC_In real type", Left_Op);
            end if;

            return Match;
         end Match_Alternative_Non_Discrete;

         --  Local variables

         Left_Op  : constant Node_Id := Left_Opnd (N);
         Right_Op :          Node_Id := Right_Opnd (N);
         Left_Val :          Value_Type;
         Match    :          Boolean := False;
      begin

         --  Discrete types
         if Is_Discrete_Type (Etype (Left_Op)) then
            Left_Val := RAC_Expr (Left_Op);

            if Right_Op /= Empty then
               Match := Match_Alternative (Left_Val, Right_Op);
            else
               Right_Op := First (Alternatives (N));
               while not Match and then Present (Right_Op) loop
                  Match := Match_Alternative (Left_Val, Right_Op);
                  Next (Right_Op);
               end loop;
            end if;

         --  Non-discrete types
         else
            if Right_Op /= Empty then
               Match := Match_Alternative_Non_Discrete (Left_Op, Right_Op);
            else
               Right_Op := First (Alternatives (N));
               while not Match and then Present (Right_Op) loop
                  Match :=
                    Match_Alternative_Non_Discrete (Left_Op, Right_Op);
                  Next (Right_Op);
               end loop;
            end if;
         end if;

         if Negate then
            Match := not Match;
         end if;

         return Boolean_Value (Match, Etype (N));
      end RAC_In;

      --------------------
      -- RAC_Op_Compare --
      --------------------

      function RAC_Op_Compare (Left, Right : Value_Type) return Boolean is
      begin
         case N_Op_Compare (Nkind (N)) is
            when N_Op_Eq =>
               return Left = Right;
            when N_Op_Ne =>
               return Left /= Right;
            when others =>
               if Is_Array_Type (Etype (Left_Opnd (N))) then
                  RAC_Unsupported ("RAC_Op_Compare on arrays", N);
               else
                  declare
                     L : constant Big_Integer := Value_Enum_Integer (Left);
                     R : constant Big_Integer := Value_Enum_Integer (Right);
                  begin
                     case N_Op_Compare (Nkind (N)) is
                        when N_Op_Lt => return L < R;
                        when N_Op_Le => return L <= R;
                        when N_Op_Ge => return L >= R;
                        when N_Op_Gt => return L > R;
                        when others  => raise Program_Error;
                     end case;
                  end;
               end if;
         end case;
      end RAC_Op_Compare;

      ------------------
      -- RAC_Unary_Op --
      ------------------

      function RAC_Unary_Op return Value_Type is
         Right : constant Value_Type := RAC_Expr (Right_Opnd (N));
      begin
         case Nkind (N) is
            when N_Op_Abs   =>
               return Integer_Value (abs Value_Integer (Right), N);

            when N_Op_Minus =>
               return Integer_Value (-Value_Integer (Right), N);

            when N_Op_Plus  =>
               return Integer_Value (+Value_Integer (Right), N);

            when N_Op_Not   =>
               if Is_Boolean_Type (Etype (N)) then
                  return Boolean_Value (not Value_Boolean (Right), Etype (N));
               else
                  RAC_Unsupported ("RAC_Unary_Op N_Op_Not", N);
               end if;

            when others =>
               raise Program_Error;
         end case;
      end RAC_Unary_Op;

      --  Local variables

      Res : Value_Type;

   --  Start of processing for RAC_Expr

   begin
      RAC_Trace ("expr " & Node_Kind'Image (Nkind (N)), N);
      Check_Supported_Type (Ty);
      Check_Fuel_Decrease (Ctx.Fuel);

      if Is_Incomplete_Or_Private_Type (Ty) then
         RAC_Incomplete ("expr with private type");
      end if;

      case Nkind (N) is
         when N_Integer_Literal =>
            Res := Integer_Value (From_String (UI_Image (Intval (N))), N);

         when N_Character_Literal =>
            Res := Enum_Value (N, Etype (N));

         when N_String_Literal =>
            Res := String_Value (Stringt.To_String (Strval (N)));

         when N_Identifier | N_Expanded_Name =>
            declare
               E : constant Entity_Id := SPARK_Atree.Entity (N);
            begin
               if Ekind (E) = E_Enumeration_Literal then
                  Res := Enum_Value (E, Etype (N));
               elsif Is_Discriminal (E)
                 or else Is_Protected_Component_Or_Discr_Or_Part_Of (E)
               then
                  RAC_Incomplete ("protected component or part of variable");
               else
                  Res := Find_Binding (E).all;
               end if;
            end;

         when N_Attribute_Reference =>
            Res := RAC_Attribute_Reference;

         when N_Binary_Op =>
            Res := RAC_Binary_Op;

         when N_Unary_Op =>
            Res := RAC_Unary_Op;

         when N_And_Then =>
            Res :=
              Boolean_Value
                (Value_Boolean (RAC_Expr (Left_Opnd (N)))
                 and then
                 Value_Boolean (RAC_Expr (Right_Opnd (N))), Etype (N));

         when N_Or_Else =>
            Res :=
              Boolean_Value
                (Value_Boolean (RAC_Expr (Left_Opnd (N)))
                 or else
                 Value_Boolean (RAC_Expr (Right_Opnd (N))), Etype (N));

         when N_Function_Call =>
            if Nkind (Name (N)) not in N_Identifier | N_Expanded_Name then
               RAC_Unsupported ("RAC_Procedure_Call name", Name (N));
            end if;

            Res := RAC_Call (N, Entity (Name (N))).Content;

         when N_In =>
            Res := RAC_In;

         when N_Not_In =>
            return RAC_In (Negate => True);

         when N_If_Expression =>
            Res := RAC_If_Expression;

         when N_Qualified_Expression =>
            Res := RAC_Expr (Expression (N), Entity (Subtype_Mark (N)));

         when N_Type_Conversion =>

            --  ??? Do we handle array conversions then?

            if Is_Record_Type (Entity (Subtype_Mark (N))) then
               RAC_Unsupported ("Type conversion between record types", N);
            end if;
            Res := RAC_Expr (Expression (N), Entity (Subtype_Mark (N)));

         when N_Aggregate | N_Delta_Aggregate =>
            Res := RAC_Aggregate;

         when N_Selected_Component =>
            declare
               Prefix_Value : constant Value_Type := RAC_Expr (Prefix (N));
               Comp         : constant Entity_Id :=
                 Search_Component_In_Type
                   (Prefix_Value.AST_Ty, Entity (Selector_Name (N)));
            begin
               pragma Assert (Present (Comp));
               if not Prefix_Value.Record_Fields.Contains (Comp) then
                  pragma Assert (Has_Discriminants (Prefix_Value.AST_Ty));
                  RAC_Failure (N, VC_Discriminant_Check);
               end if;
               Res := Prefix_Value.Record_Fields (Comp).all;
            end;

         when N_Indexed_Component =>
            declare
               A : constant Value_Type := RAC_Expr (Prefix (N));
               E : constant Node_Id := First (Expressions (N));
               V : constant Value_Type := RAC_Expr (E);
               I : constant Big_Integer := Value_Enum_Integer (V);

            begin
               if Present (Next (E)) then
                  RAC_Unsupported
                    ("RAC_Expr multidimensional array access", N);
               end if;

               declare
                  C : constant Big_Integer_To_Value_Maps.Cursor :=
                    A.Array_Values.Find (I);
               begin
                  if I < A.First_Attr.Content
                    or else A.Last_Attr.Content < I
                  then
                     --  ??? The index check VC is generated for the first
                     --  expr
                     RAC_Failure (E, VC_Index_Check);
                  end if;

                  if Big_Integer_To_Value_Maps.Has_Element (C) then
                     Res := A.Array_Values (C).all;
                  elsif A.Array_Others = null then
                     RAC_Incomplete ("missing value for OTHERS in array");
                  else
                     Res := Copy (A.Array_Others.all);
                  end if;
               end;
            end;

         when N_Quantified_Expression =>
            declare
               Break : exception;
               procedure Iteration;

               ---------------
               -- Iteration --
               ---------------

               procedure Iteration is
                  B : constant Boolean :=
                        Value_Boolean (RAC_Expr (Condition (N)));
               begin
                  if All_Present (N) xor B then
                     raise Break;
                  end if;
               end Iteration;

            begin
               if Present (Loop_Parameter_Specification (N)) then
                  begin
                     Iterate_Loop_Param_Spec
                       (Loop_Parameter_Specification (N), Iteration'Access);
                     Res := Boolean_Value (All_Present (N), Etype (N));
                  exception
                     when Break =>
                        Res := Boolean_Value
                          (not (All_Present (N)), Etype (N));
                  end;
               else
                  pragma Assert (Present (Iterator_Specification (N)));
                  RAC_Unsupported ("RAC_Expr quantified expression", N);
               end if;
            end;

         when N_Case_Expression =>
            declare
               Alternative : Node_Id;
            begin
               Match_Case_Alternative (N, Alternative);
               Res := RAC_Expr (Expression (Alternative));
            end;

         when N_Slice =>
            declare
               Base_Array : constant Value_Type := RAC_Expr (Prefix (N));
               Idx_Range  : constant Node_Id := Get_Range (Discrete_Range (N));
               Low        : constant Big_Integer :=
                 Value_Enum_Integer (RAC_Expr (Low_Bound (Idx_Range)));
               High       : constant Big_Integer :=
                 Value_Enum_Integer (RAC_Expr (High_Bound (Idx_Range)));
            begin
               Res := (K            => Array_K,
                       AST_Ty       => Ty,
                       First_Attr   => (Present => True, Content => Low),
                       Last_Attr    => (Present => True, Content => High),
                       Array_Values => Big_Integer_To_Value_Maps.Empty,
                       Array_Others => Base_Array.Array_Others);

               if Low > High then
                  return Res;

               else
                  for C in Base_Array.Array_Values.Iterate loop
                     declare
                        K : constant Big_Integer :=
                          Big_Integer_To_Value_Maps.Key (C);
                     begin
                        if Low <= K and then K <= High then
                           Res.Array_Values.Insert
                             (K, Big_Integer_To_Value_Maps.Element (C));
                        end if;
                     end;
                  end loop;
               end if;
            end;

         when others =>
            RAC_Unsupported ("RAC_Expr", N);
      end case;

      if Is_Integer_Type (Ty) then
         Check_Integer (Res, Ty, N);
      end if;

      return Res;
   end RAC_Expr;

   ------------------
   -- RAC_Expr_LHS --
   ------------------

   function RAC_Expr_LHS (N : N_Subexpr_Id) return Value_Access is
   begin
      RAC_Trace ("expr lhs " & Node_Kind'Image (Nkind (N)), N);
      case Nkind (N) is
         when N_Identifier | N_Expanded_Name =>
            return Find_Binding (SPARK_Atree.Entity (N));

         when N_Type_Conversion =>
            return RAC_Expr_LHS (Expression (N));

         when N_Selected_Component =>
            return
              RAC_Expr_LHS (Prefix (N)).all.Record_Fields
                (Entity (Selector_Name (N)));

         when N_Indexed_Component =>
            declare
               A : constant Value_Access := RAC_Expr_LHS (Prefix (N));
               E : constant Node_Id := First (Expressions (N));
               V : constant Value_Type := RAC_Expr (E);
               I : constant Big_Integer := Value_Enum_Integer (V);
               C : Big_Integer_To_Value_Maps.Cursor := A.Array_Values.Find (I);
               B : Boolean;
            begin
               if Present (Next (E)) then
                  RAC_Unsupported
                    ("RAC_Expr_LHS multidimensional array access", N);
               end if;

               if I < A.First_Attr.Content or else A.Last_Attr.Content < I then
                  --  ??? The index check VC is generated for the first expr
                  RAC_Failure (E, VC_Index_Check);
               end if;

               if not Big_Integer_To_Value_Maps.Has_Element (C)
               then
                  if A.Array_Others = null then
                     RAC_Incomplete ("missing value for OTHERS in array");
                  else
                     A.Array_Values.Insert
                       (I,
                        new Value_Type'(Copy (A.Array_Others.all)),
                        C,
                        B);
                  end if;
               end if;

               return A.Array_Values (C);
            end;

         when others =>
            RAC_Unsupported ("RAC_Expr_LHS", N);
      end case;
   end RAC_Expr_LHS;

   -----------------
   -- RAC_Failure --
   -----------------

   procedure RAC_Failure (N : Node_Id; K : VC_Kind) is
   begin
      Exn_RAC_Result := Some_Result
        ((Res_Kind    => Res_Failure,
          Res_Node    => N,
          Res_VC_Kind => K,
          Res_VC_Id   => <>));
      raise Exn_RAC_Failure;
   end RAC_Failure;

   --------------------
   -- RAC_Incomplete --
   --------------------

   procedure RAC_Incomplete (Reason : String) is
   begin
      Exn_RAC_Result := Some_Result
        ((Res_Kind   => Res_Incomplete,
          Res_Reason => To_Unbounded_String (Reason)));
      raise Exn_RAC_Incomplete;
   end RAC_Incomplete;

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) is
   begin
      if Do_RAC_Info then
         Write_Str ("RAC info: " & Ctx & " " & Msg & " at ");
         Write_Location (Sloc (N));
         Write_Eol;
      end if;
   end RAC_Info;

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Msg : String) is
   begin
      if Do_RAC_Info then
         Write_Line ("RAC info: " & Msg);
      end if;
   end RAC_Info;

   --------------
   -- RAC_List --
   --------------

   procedure RAC_List (L : List_Id) is
      N : Node_Id := First (L);
   begin
      while Present (N) loop
         RAC_Node (N);
         Next (N);
      end loop;
   end RAC_List;

   --------------
   -- RAC_Node --
   --------------

   procedure RAC_Node (N : Node_Id) is
      Ignore : Opt_Value_Type;
   begin
      RAC_Trace ("node " & Node_Kind'Image (Nkind (N)), N);
      Check_Fuel_Decrease (Ctx.Fuel);

      if Nkind (N) not in N_Ignored_In_SPARK then
         case Nkind (N) is
         when N_Handled_Sequence_Of_Statements =>

            --  Ignore exception handler, they cannot occur in SPARK code

            RAC_List (Statements (N));
         when N_Procedure_Call_Statement =>
            Ignore :=
              RAC_Call (N, Entity (Name (N)));
         when N_Pragma =>
            RAC_Pragma (N);
         when others =>
            RAC_Statement (N);
         end case;
      end if;
   end RAC_Node;

   ----------------
   -- RAC_Pragma --
   ----------------

   procedure RAC_Pragma (N : N_Pragma_Id) is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (N));
      Desc : constant String :=
        Get_Name_String (Chars (Pragma_Identifier (N)));
   begin
      case Get_Pragma_Id (N) is
         when Pragma_Check =>
            Check_Node (Expression (Next (Arg1)), Desc, VC_Assert);
         when others =>
            RAC_Unsupported ("RAC_Pragma", N);
      end case;
   end RAC_Pragma;

   ----------------
   -- RAC_Return --
   ----------------

   procedure RAC_Return (V : Opt_Value_Type) is
   begin
      Exn_RAC_Return_Value := new Opt_Value_Type'(V);
      raise Exn_RAC_Return;
   end RAC_Return;

   -------------------
   -- RAC_Statement --
   -------------------

   procedure RAC_Statement (N : Node_Id) is

      procedure Assignment_To_Slice (A, RHS : Value_Access);
      --  Fill the part of the array designated by the slice bounds with the
      --  elements of RHS.

      -------------------------
      -- Assignment_To_Slice --
      -------------------------

      procedure Assignment_To_Slice (A, RHS : Value_Access)
      is
         package Idx_Set is new
           Indefinite_Ordered_Sets
             (Element_Type => Big_Integer);

         To_Update :          Idx_Set.Set;
         Curr      :          Big_Integer  := RHS.First_Attr.Content;
         Last      : constant Big_Integer  := RHS.Last_Attr.Content;
      begin

         --  For the indices included in the slice's range, update the values
         --  of the elements which already have a specified value in
         --  Array_Values.

         while Curr <= Last loop
            To_Update.Insert (Curr);
            Curr := Curr + 1;
         end loop;

         for C in RHS.Array_Values.Iterate loop
            declare
               K : constant Big_Integer :=
                 Big_Integer_To_Value_Maps.Key (C);
               E : constant Value_Access :=
                 Big_Integer_To_Value_Maps.Element (C);
            begin
               if E /= A.Array_Others then
                  A.Array_Values.Include (K, new Value_Type'(Copy (E.all)));
               end if;

               To_Update.Delete (K);
            end;
         end loop;

         if RHS.Array_Others /= A.Array_Others
           and then To_Update.Length > 0
         then
            if RHS.Array_Others = null then
               RAC_Incomplete ("missing value for OTHERS in array");
            else
               for C in To_Update.Iterate loop
                  A.Array_Values.Include
                    (To_Update (C),
                     new Value_Type'(Copy (RHS.Array_Others.all)));
               end loop;
            end if;
         end if;
      end Assignment_To_Slice;

   begin
      case Nkind (N) is
         when N_Ignored_In_SPARK =>
            null;

         when N_Simple_Return_Statement =>
            if Present (Expression (N)) then
               declare
                  Ty  : constant Type_Kind_Id :=
                    Retysp
                      (Etype
                         (Return_Applies_To (Return_Statement_Entity (N))));
                  Res : constant Value_Type :=
                    Copy (RAC_Expr (Expression (N), Ty));
               begin
                  RAC_Return (Some_Value (Res));
               end;
            else
               RAC_Return (No_Value);
            end if;

         when N_Assignment_Statement =>
            declare
               Ty  : constant Entity_Id := Retysp (Etype (Name (N)));
               RHS : constant Value_Access :=
                 new Value_Type'(Copy (RAC_Expr (Expression (N), Ty)));

            begin
               --  Slide the array value if necessary

               if RHS.K = Array_K and then Is_Constrained (Ty) then
                     Slide (RHS.all, Ty);
               end if;

               --  Perform discriminant check

               if Has_Discriminants (Ty)
                 and then not Has_Defaulted_Discriminants (Ty)
               then
                  declare
                     LHS   : Value_Type := (K => Record_K, others => <>);
                     Discr : Entity_Id;
                     Elmt  : Elmt_Id;

                  begin
                     if Is_Constrained (Ty) then
                        Discr := First_Discriminant (Root_Retysp (Ty));
                        Elmt := First_Elmt (Discriminant_Constraint (Ty));
                        while Present (Discr) loop
                           LHS.Record_Fields.Insert
                             (Discr,
                              new Value_Type'
                                (RAC_Expr
                                     (Node (Elmt), Retysp (Etype (Discr)))));
                           Next_Elmt (Elmt);
                           Next_Discriminant (Discr);
                        end loop;
                     else
                        LHS := RAC_Expr (Name (N), Ty);
                     end if;

                     Discr := First_Discriminant (Root_Retysp (Ty));
                     while Present (Discr) loop
                        if LHS.Record_Fields (Discr).all /=
                          RHS.Record_Fields (Discr).all
                        then
                           RAC_Failure (N, VC_Discriminant_Check);
                        end if;
                        Next_Discriminant (Discr);
                     end loop;
                  end;
               end if;

               case Nkind (Name (N)) is
                  when N_Identifier | N_Expanded_Name =>
                     Update_Value (Ctx.Env, Entity (Name (N)), RHS);

                  when N_Selected_Component =>
                     declare
                        LHS : constant Value_Access :=
                          RAC_Expr_LHS (Prefix (Name (N)));
                        E   : constant Entity_Id :=
                          Search_Component_In_Type
                            (LHS.AST_Ty, Entity (Selector_Name (Name (N))));
                     begin
                        pragma Assert (Present (E));

                        if not LHS.Record_Fields.Contains (E) then
                           if Is_Class_Wide_Type (LHS.AST_Ty) then
                              RAC_Incomplete ("classwide type");
                           else
                              pragma Assert (Has_Discriminants (LHS.AST_Ty));
                              RAC_Failure
                                (Prefix (Name (N)), VC_Discriminant_Check);
                           end if;
                        end if;
                        LHS.Record_Fields.Include (E, RHS);
                     end;

                  when N_Indexed_Component =>
                     declare
                        A : constant Value_Access :=
                          RAC_Expr_LHS (Prefix (Name (N)));
                        E : constant Node_Id :=
                          First (Expressions (Name (N)));
                        I : constant Big_Integer :=
                          Value_Enum_Integer (RAC_Expr (E));
                     begin
                        if Present (Next (E)) then
                           RAC_Unsupported
                             ("RAC_Expr assignment", "many indices");
                        end if;

                        if I < A.First_Attr.Content
                          or else A.Last_Attr.Content < I
                        then
                           --  ??? Index check VC is generated for the 1st
                           --  expr
                           RAC_Failure (E, VC_Index_Check);
                        end if;

                        --  Only specify a component association if the value
                        --  being assigned is not already that of "others".
                        --  Update the value if the component association
                        --  already exists.

                        if A.Array_Values.Contains (I)
                          or else RHS /= A.Array_Others
                        then
                           A.Array_Values.Include (I, RHS);
                        end if;
                     end;

                  when N_Slice =>
                     Assignment_To_Slice (RAC_Expr_LHS (Prefix (Name (N))),
                                          RHS);

                  when others =>
                     RAC_Unsupported ("N_Assignment_Statement", Name (N));
               end case;
            end;

         when N_If_Statement =>
            if Value_Boolean (RAC_Expr (Condition (N))) then
               RAC_List (Then_Statements (N));
            else
               declare
                  Elsif_Part : Node_Id := First (Elsif_Parts (N));
                  In_Elsif   : Boolean := False;
               begin
                  while Present (Elsif_Part) loop
                     if Value_Boolean (RAC_Expr (Condition (Elsif_Part)))
                     then
                        RAC_List (Then_Statements (Elsif_Part));
                        In_Elsif := True;
                        exit;
                     end if;
                     Next (Elsif_Part);
                  end loop;

                  if not In_Elsif and then Present (Else_Statements (N)) then
                     RAC_List (Else_Statements (N));
                  end if;
               end;
            end if;

         when N_Loop_Statement =>
            declare
               Scheme           : constant Node_Id := Iteration_Scheme (N);
               Loop_Entry_Nodes : Node_Sets.Set;
            begin
               --  Collect prefixes of all 'Loop_Entry attribute uses and store
               --  the result of their evaluation.

               Collect_Attr_Parts (N,
                                   Snames.Name_Loop_Entry,
                                   Loop_Entry_Nodes);
               Evaluate_Attribute_Prefix_Values (Snames.Name_Loop_Entry,
                                                 Loop_Entry_Nodes);

               if No (Scheme) then
                  begin
                     loop
                        RAC_List (Statements (N));
                        pragma Annotate
                          (CodePeer, Intentional,
                           "loop does not complete normally",
                           "RAC signals loop exit through Exn_RAC_Exit");
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;

               elsif Present (Condition (Scheme)) then
                  --  while Condition loop Statements end loop;
                  begin
                     while
                       Value_Boolean (RAC_Expr (Condition (Scheme)))
                     loop
                        RAC_List (Statements (N));
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;

               elsif Present (Loop_Parameter_Specification (Scheme)) then
                  declare
                     procedure Iteration;
                     procedure Iteration is
                     begin
                        RAC_List (Statements (N));
                     end Iteration;
                  begin
                     Iterate_Loop_Param_Spec
                       (Loop_Parameter_Specification (Scheme),
                        Iteration'Access);
                  end;
               else
                  pragma Assert (Present (Iterator_Specification (Scheme)));
                  RAC_Unsupported ("RAC_Statement loop iterator", N);
               end if;

               --  Clean the nearest scope by removing 'Loop_Entry values
               for N of Loop_Entry_Nodes loop
                  Ctx.Env (Ctx.Env.First).Loop_Entry_Attrs.Delete (N);
               end loop;
            end;

         when N_Exit_Statement =>
            if Present (Name (N)) then
               RAC_Unsupported ("RAC_Statement exit statement with name", N);
            end if;

            if No (Condition (N))
              or else Value_Boolean (RAC_Expr (Condition (N)))
            then
               raise Exn_RAC_Exit;
            end if;

         when N_Block_Statement =>
            Ctx.Env.Prepend (Scopes'(others => <>));
            RAC_Decls (Declarations (N));
            RAC_Node (Handled_Statement_Sequence (N));
            Ctx.Env.Delete_First;

         when N_Case_Statement =>
            declare
               Alternative : Node_Id;
            begin
               Match_Case_Alternative (N, Alternative);
               RAC_List (Statements (Alternative));
            end;

         when others =>
            RAC_Unsupported ("RAC_Statement", N);
      end case;
   end RAC_Statement;

   ---------------
   -- RAC_Stuck --
   ---------------

   procedure RAC_Stuck (Reason : String) is
   begin
      Exn_RAC_Result := Some_Result
        ((Res_Kind   => Res_Stuck,
          Res_Reason => To_Unbounded_String (Reason)));
      raise Exn_RAC_Stuck;
   end RAC_Stuck;

   ---------------
   -- RAC_Trace --
   ---------------

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) is
   begin
      if Do_RAC_Trace then
         Write_Str ("RAC trace: " & Msg);
         if Present (N) then
            Write_Str (" at ");
            Write_Location (Sloc (N));
         end if;
         Write_Eol;
      end if;
   end RAC_Trace;

   ---------------------
   -- RAC_Unsupported --
   ---------------------

   procedure RAC_Unsupported (Str : String; Str1 : String) is
      Msg : constant String := Str & " not supported for " & Str1;
   begin
      if Do_RAC_Info then
         Write_Line ("TODO: " & Msg);
      end if;
      RAC_Incomplete (Msg);
   end RAC_Unsupported;

   procedure RAC_Unsupported (Str : String; N : Node_Id) is
      Str1 : Unbounded_String;
   begin
      if Do_RAC_Info then
         Write_Line ("Unsupported: " & Str);
         Treepr.Print_Tree_Node (N, "Unsupported: ");
         Call_Stack;
      end if;

      Append (Str1, "node kind " & Node_Kind'Image (Nkind (N)));

      if Present (N) then
         Append (Str1, " at ");
         Append (Str1, File_Name (Sloc (N)));
         Append (Str1, ':');
         Append (Str1, Physical_Line_Number'Image
                 (Get_Physical_Line_Number (Sloc (N))));
      end if;

      RAC_Unsupported (Str, To_String (Str1));
   end RAC_Unsupported;

   ------------------
   -- Record_Value --
   ------------------

   function Record_Value
     (F  : Entity_To_Value_Maps.Map;
      Ty : Entity_Id) return Value_Type
   is
   begin
      if Present (Ty) then
         Check_Supported_Type (Ty);
      end if;
      return (K                => Record_K,
              Record_Fields    => F,
              Constrained_Attr => <>,
              AST_Ty           => Ty);
   end Record_Value;

   ---------------
   -- Set_Value --
   ---------------

   procedure Set_Value
     (S : in out Scopes;
      E :        Entity_Id;
      V :        Value_Access)
   is
      C   : Entity_Bindings.Cursor;
      Ins : Boolean;
   begin
      S.Bindings.Insert (E, V, C, Ins);

      if not Ins then
         S.Bindings (C) := V;
      end if;
   end Set_Value;

   ------------------
   -- String_Value --
   ------------------

   function String_Value (Str : String) return Value_Type is
      Other  : constant Value_Access :=
        new Value_Type'(Default_Value (Standard_Character));
      Values : Big_Integer_To_Value_Maps.Map;
      First  : constant Big_Integer := To_Big_Integer (Str'First);
      Last   : constant Big_Integer := To_Big_Integer (Str'Last);
   begin
      for I in Str'Range loop
         Values.Insert
           (To_Big_Integer (I),
            new Value_Type'(Enum_Value
              (UI_From_Int (Character'Pos (Str (I))), Standard_Character)));
      end loop;
      return Array_Value (First, Last, Values, Other, Standard_String);
   end String_Value;

   -------------------
   -- To_Long_Float --
   -------------------

   function To_Long_Float (B : Big_Integer) return Long_Float is
      package Long_Float_Conversions is new
        Ada.Numerics.Big_Numbers.Big_Reals.Float_Conversions (Long_Float);
   begin
      return Long_Float_Conversions.From_Big_Real
        (Ada.Numerics.Big_Numbers.Big_Reals.To_Big_Real (B));
   exception
      when Constraint_Error =>
         RAC_Incomplete ("Integer too large: " & To_String (B));
   end To_Long_Float;

   ----------------
   -- To_Integer --
   ----------------

   function To_Integer (B : Big_Integer) return Integer is
   begin
      return Ada.Numerics.Big_Numbers.Big_Integers.To_Integer (B);
   exception
      when Constraint_Error =>
         RAC_Incomplete ("Integer too large: " & To_String (B));
   end To_Integer;

   ---------------
   -- To_String --
   ---------------

   function To_String (Res : Result) return String is
     (case Res.Res_Kind is
         when Res_Normal       =>
            "NORMAL" & (if Res.Res_Value.Present then
             " (" & To_String (Res.Res_Value.Content) & ")" else ""),
         when Res_Failure      =>
            "FAILURE (" &
            VC_Kind'Image (Res.Res_VC_Kind) &
            " at " & File_Name (Sloc (Res.Res_Node)) & ":" &
            Int'Image (Int (Get_Logical_Line_Number (Sloc (Res.Res_Node)))) &
            ")",
         when Res_Stuck        =>
            "STUCK (" & To_String (Res.Res_Reason) & ")",
         when Res_Incomplete   =>
            "INCOMPLETE (" & To_String (Res.Res_Reason) & ")",
         when Res_Not_Executed =>
            "NOT EXECUTED");

   function To_String (S : Scopes) return String is
      Res : Unbounded_String;

      procedure Append_Attrs (Attr : String; M : Node_To_Value.Map);
      --  Append mappings of attributes Attr in M

      ------------------
      -- Append_Attrs --
      ------------------

      procedure Append_Attrs (Attr : String; M : Node_To_Value.Map) is
         First : Boolean := True;
      begin
         for C in M.Iterate loop
            if not First then
               Append (Res, ", ");
            end if;
            Append (Res, Attr);
            Append (Res, " (" & Node_Id'Image (Node_To_Value.Key (C)) & ")");
            Append (Res, " = " & To_String (M (C)));
            First := False;
         end loop;
      end Append_Attrs;

      First : Boolean := True;

   begin
      for C in S.Bindings.Iterate loop
         if not First then
            Append (Res, ", ");
         end if;
         Append (Res, Get_Name_String (Chars (Entity_Bindings.Key (C))));
         Append (Res, " (" & Entity_Id'Image (Entity_Bindings.Key (C)) & ")");
         Append (Res, " = " & To_String (S.Bindings (C).all));
         First := False;
      end loop;

      Append_Attrs ("Old", S.Old_Attrs);
      Append_Attrs ("Loop_Entry", S.Loop_Entry_Attrs);

      return To_String (Res);
   end To_String;

   function To_String (E : Environments.Vector) return String is
      Res   : Unbounded_String;
      First : Boolean := True;
   begin
      for S of E loop
         if not First then
            Append (Res, "; ");
         end if;
         Append (Res, To_String (S));
         First := False;
      end loop;

      return To_String (Res);
   end To_String;

   ------------------
   -- Update_Value --
   ------------------

   procedure Update_Value
     (Env : in out Environments.Vector;
      E   :        Entity_Id;
      V   :        Value_Access)
   is
      BC : Entity_Bindings.Cursor;
   begin
      for Scope of Env loop
         BC := Scope.Bindings.Find (E);

         if Entity_Bindings.Has_Element (BC) then
            Scope.Bindings (BC) := V;
            return;
         end if;
      end loop;

      --  E must be a global constant without variable input (otherwise it
      --  would have been initialized in Init_Global).
      pragma Assert (if Ekind (E) = E_Constant
                     and then not Is_Access_Variable (Etype (E))
                     then not Has_Variable_Input (E));

      Env (Env.Last).Bindings.Insert (E, V);
   end Update_Value;

   -------------------
   -- Value_Boolean --
   -------------------

   function Value_Boolean (V : Value_Type) return Boolean is
   begin
      if V.K /= Scalar_K
        or else V.Scalar_Content = null
        or else V.Scalar_Content.K /= Enum_K
      then
         raise Program_Error with "Value_Boolean";
      end if;

      if V.Scalar_Content.Enum_Entity = Standard_True then
         return True;
      elsif V.Scalar_Content.Enum_Entity = Standard_False then
         return False;
      else
         raise Program_Error with "Value_Boolean";
      end if;
   end Value_Boolean;

   ---------------------
   -- Value_Character --
   ---------------------

   function Value_Character (V : Value_Type) return Character is
   begin
      if V.K /= Scalar_K
        or else V.Scalar_Content = null
        or else V.Scalar_Content.K /= Enum_K
      then
         raise Program_Error with "Value_Character";
      end if;

      return Character'Val
        (To_Integer (Char_Literal_Value (V.Scalar_Content.Enum_Entity)));
   end Value_Character;

   ------------------------
   -- Value_Enum_Integer --
   ------------------------

   function Value_Enum_Integer (V : Value_Type) return Big_Integer is
   begin
      if V.K /= Scalar_K or else V.Scalar_Content = null then
         raise Program_Error with "Value_Enum_Integer";
      end if;

      case V.Scalar_Content.K is
         when Integer_K =>
            return V.Scalar_Content.Integer_Content;
         when Enum_K    =>
            return To_Big_Integer
              (Enum_Entity_To_Integer (V.Scalar_Content.Enum_Entity));
         when others =>
            raise Program_Error with "Value_Enum_Integer";
      end case;
   end Value_Enum_Integer;

   -------------------
   -- Value_Integer --
   -------------------

   function Value_Integer (V : Value_Type) return Big_Integer is
   begin
      if V.K /= Scalar_K
        or else V.Scalar_Content = null
        or else V.Scalar_Content.K /= Integer_K
      then
         raise Program_Error with "Value_Integer";
      end if;

      return V.Scalar_Content.Integer_Content;
   end Value_Integer;

end CE_RAC;
