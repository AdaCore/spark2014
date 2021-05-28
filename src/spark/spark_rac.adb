------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2021, AdaCore                       --
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

with Ada.Characters.Handling; use Ada.Characters.Handling;
with Ada.Containers.Indefinite_Vectors;
with Ada.Environment_Variables;
with Ada.Strings;             use Ada.Strings;
with Ada.Strings.Fixed;       use Ada.Strings.Fixed;
with Ada.Text_IO;             use Ada.Text_IO;
with Atree;                   use Atree;
with Einfo.Entities;          use Einfo.Entities;
with Einfo.Utils;             use Einfo.Utils;
with Flow_Refinement;         use Flow_Refinement;
with Flow_Types;              use Flow_Types;
with Flow_Utility;            use Flow_Utility;
with GNAT.Traceback;
with GNAT.Traceback.Symbolic;
with GNATCOLL.JSON;           use GNATCOLL.JSON;
with GNATCOLL.Utils;          use GNATCOLL.Utils;
with Gnat2Why.CE_Utils;       use Gnat2Why.CE_Utils;
with Gnat2Why_Opts.Reading;
with Gnat2Why.Util;           use Gnat2Why.Util;
with Hashing;                 use Hashing;
with Namet;                   use Namet;
with Nlists;                  use Nlists;
with Nmake;                   use Nmake;
with Output;                  use Output;
with Sem_Aux;                 use Sem_Aux;
with Sem_Util;                use Sem_Util;
with Sinfo.Nodes;             use Sinfo.Nodes;
with Sinfo.Utils;             use Sinfo.Utils;
with Sinput;                  use Sinput;
with Snames;                  use Snames;
with SPARK_Atree;
with SPARK_Definition;
with SPARK_Util;              use SPARK_Util;
with SPARK_Util.Subprograms;  use SPARK_Util.Subprograms;
with SPARK_Util.Types;        use SPARK_Util.Types;
with Stand;                   use Stand;
with Stringt;
with Treepr;
with Uintp;                   use Uintp;

package body SPARK_RAC is

   -----------
   -- Types --
   -----------

   procedure Check_Supported_Type (Ty : Node_Id);
   --  Call RAC_Unsupported if Ty is not supported yet

   function Safe_Retysp (T : Type_Kind_Id) return Entity_Id is
     (if SPARK_Definition.Entity_Marked (T) then
         Retysp (T)
      else T);
   --  Apply Retysp safely

   ------------
   -- Values --
   ------------

   function No_Value return Opt_Value is
     (Present => False);
   --  Absence of an optional value

   function Some_Value (V : Value) return Opt_Value is
     (Present => True, Content => V);
   --  Presence of an optional value

   function Enum_Value (E : Entity_Id) return Value is
     (Ty => Ty_Enum, Enum_Entity => E);
   --  Make an enum value from an enumeration literal E

   function String_Value (S : Unbounded_String) return Value is
     (Ty => Ty_String, String_Content => S);

   function String_Value (S : String) return Value is
     (String_Value (To_Unbounded_String (S)));

   function Enum_Value (I : Uint; Ty : Entity_Id) return Value;
   --  Make an enum value from an enum index I

   function Record_Value (F : Fields.Map; Ty : Entity_Id) return Value;
   --  Make a record value with fields F

   function Array_Value
     (First, Last : Big_Integer;
      Values      : Values_Map.Map;
      Other       : Value_Access)
      return Value
   is
     (Ty           => Ty_Array,
      Array_First  => First,
      Array_Last   => Last,
      Array_Values => Values,
      Array_Others => Other);
   --  Make an array value

   function Boolean_Value (B : Boolean) return Value;
   --  Make a boolean value, i.e. an enum value

   function Value_Boolean (V : Value) return Boolean;
   --  Get the value of a boolean enum value, fail for other types

   function Value_Enum_Integer (V : Value) return Big_Integer;
   --  Shortcut to convert an enum or integer value to an integer (using the
   --  position of the enum literal for enum values).

   function Value_Integer (V : Value) return Big_Integer;
   --  Get the value of an integer value, fail for other types

   function Value_String (V : Value) return String;
   --  Get the value of a string value, fail for other types;

   function To_Integer (I : Uint) return Integer is
     (Integer (UI_To_Int (I)));
   --  Shortcut to convert an Uint to an Integer

   function To_Big_Integer (I : Uint) return Big_Integer is
     (To_Big_Integer (To_Integer (I)));
   --  Shortcut to convert an Uint to a Big_Integer

   function To_Integer (B : Big_Integer) return Integer;
   --  Convert big integer to integer, raise RAC_Incomplete when out of range

   procedure Check_Integer (I : Big_Integer; Ty : Entity_Id; N : Node_Id);
   --  Check an integer I against the range bounds or apply modulo for type Ty,
   --  signaling errors for node N.

   procedure Check_Integer (V : Value; Ty : Entity_Id; N : Node_Id);
   --  Check a value V against the range bounds or apply modulo of the type Ty,
   --  if V is an integer, signaling errors for node N.

   function Integer_Value (I : Big_Integer) return Value is
      (Ty => Ty_Integer, Integer_Content => I);

   function Integer_Value
     (I  : Big_Integer;
      Ty : Entity_Id;
      N  : Node_Id)
      return Value;
   --  Construct an integer value after checking against type bounds or
   --  applying modulo for type Ty, signaling errors for node N.

   function Integer_Value (I : Big_Integer; N : Node_Id) return Value is
     (Integer_Value (I, Safe_Retysp (Etype (N)), N));
   --  Construct an integer value after checking against type bounds or
   --  applying modulo for type Etype (N), signaling errors for node N.

   function Copy (V : Value) return Value;
   --  Make a copy of a value

   function Copy (F : Fields.Map) return Fields.Map;
   --  Make a copy of record fields

   function Copy (A : Values_Map.Map) return Values_Map.Map;

   function Default_Value (Ty : Node_Id) return Value;
   --  Return the type default value

   function Enum_Entity_To_Integer (E : Entity_Id) return Uint;
   --  Convert an enum entity (enum literal entity or character literal) to an
   --  integer (enum pos for enumerations, character pos for characters).

   function Enum_Entity_To_String (E : Entity_Id) return String;
   --  Return a string for an enum entity

   function To_String
     (Fst, Lst : Big_Integer;
      M        : Values_Map.Map;
      O        : Value_Access)
      return String;
   --  Convert the fields of an array value to a string

   function To_String (F : Fields.Map) return String;
   --  Convert the fields of a record value to a string

   function "=" (F1, F2 : Fields.Map) return Boolean;

   function "=" (M1, M2 : Values_Map.Map) return Boolean;

   --------------------------------
   -- Runtime control exceptions --
   --------------------------------

   Exn_RAC_Exit : exception;
   --  Signal a loop exit

   Exn_RAC_Return : exception;
   --  Signal the return from a subprogram

   procedure RAC_Return (V : Opt_Value) with No_Return;
   --  Return from subprogram, optionally with some return value

   function Flush_RAC_Return return Opt_Value;
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

   procedure RAC_Stuck (Reason : String) with No_Return;
   --  Raise Exn_RAC_Stuck and set result, i.e. the RAC execution failed
   --  due to a false assumption.

   procedure RAC_Incomplete (Reason : String) with No_Return;
   --  Raise Exn_RAC_Incomplete and set result, i.e. the RAC execution could
   --  not complete due to technical or theoretical limitations.

   procedure RAC_Unsupported (Str : String; N : Node_Id) with No_Return;
   --  Raise Exn_RAC_Incomplete and set result, i.e. the RAC execution could
   --  not complete due to unsupported or unimplemented features.

   procedure RAC_Unsupported (Str : String; Str1 : String) with No_Return;
   --  Raise Exn_RAC_Incomplete and set result, i.e. the RAC execution could
   --  not complete due to unsupported or unimplemented features.

   Exn_RAC_Return_Value : access Opt_Value;
   --  The return value, set by RAC_Return, retrieved by Flush_RAC_Return

   --------------------------------------------
   -- The evaluation environment and context --
   --------------------------------------------

   function Name_Hash (N : Name_Id) return Hash_Type is
     (Generic_Integer_Hash (Integer (N)));

   package Attributes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Name_Id,
      Element_Type    => Value_Access,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");
   --  Attributes (e.g. X'A for X) in a map binding names to values

   type Attributes_Access is access Attributes.Map;

   function To_String (Attrs : Attributes.Map) return String;

   type Binding is record
      Val   : Value_Access;
      Attrs : Attributes_Access := new Attributes.Map'(Attributes.Empty);
   end record;
   --  A binding is a variable value and the attributes of the variable

   function To_String (B : Binding) return String;

   package Scopes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Binding,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  A scope is a flat mapping of variable (defining identifiers) to bindings

   function To_String (S : Scopes.Map) return String;

   package Environments is new Ada.Containers.Indefinite_Vectors
     (Index_Type   => Natural,
      Element_Type => Scopes.Map,
      "="          => Scopes."=");
   --  An execution environment is a stack of scopes

   function To_String (E : Environments.Vector) return String
     with Unreferenced;

   procedure Set_Value
     (S : in out Scopes.Map;
      E :        N_Defining_Identifier_Id;
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
      Fuel             : Integer;
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

   function Find_Binding
     (E   :        N_Entity_Id;
      Ctx : in out Context)
      return Binding;
   --  Find the binding of a variable in the context environment. If not found,
   --  it is assumed to be a global constant and initialised as it.

   -------------------
   -- Value oracles --
   -------------------

   function Can_Get (N : Node_Id) return Boolean is
     (Nkind (N) in N_Defining_Identifier | N_Identifier | N_Expanded_Name)
   with
     Ghost => True;
   --  Predicate for nodes, for which the counterexample may have a value

   function Import
     (V  : Cntexmp_Value;
      Ty : Entity_Id;
      N  : Node_Id)
      return Value
   with
     Pre => Can_Get (N);
   --  Import a counterexample value V of type Ty (the context of node is used
   --  only to signal errors).

   function Get_Cntexmp_Value
     (N       : Node_Id;
      Cntexmp : Cntexample_File_Maps.Map)
      return Opt_Value
   with
     Pre => Can_Get (N);
   --  Get the value of variable N from the counterexample

   type Value_Origin is (From_Counterexample, From_Expr, From_Type_Default);
   --  The origin of a value in a call to Get

   function Get_Value
     (N           :        Node_Id;
      Ex          :        Node_Id;
      Use_Default :        Boolean;
      Ctx         : in out Context;
      Origin      :    out Value_Origin)
      return Value
   with
     Pre => Can_Get (N);
   --  Get a value for variable N using the first successful of the following
   --  strategies:
   --  1) from the counterexample in the context,
   --  2) from the evaluation of an expression Ex (if present),
   --  3) or the type default (if Use_Default is True)
   --  If neither of the strategies provides a value, the function signals
   --  RAC_Incomplete.

   ---------------------------------------
   -- Check the validity of annotations --
   ---------------------------------------

   procedure Get_Bounds (N : Node_Id; Low, High : out Big_Integer);
   --  Get the low and high bounds of node N

   procedure Get_Integer_Type_Bounds
     (Ty       :     Entity_Id;
      Fst, Lst : out Big_Integer)
   with
     Pre => Is_Integer_Type (Ty);
   --  Write the first and last value of an integer type Ty in Fst and Lst

   function Get_Enum_Type_Last (Ty : Entity_Id) return Integer;
   --  Returns the index of the last enumeration literal

   procedure Get_Array_Info
     (Ty                :     Node_Id;
      Index_Ty, Comp_Ty : out Entity_Id;
      Fst, Lst          : out Big_Integer);
   --  Get the index type and component type, and the bounds of a
   --  one-dimensional, constrained array.

   procedure Check_Fuel_Decrease (Fuel : in out Integer);
   --  Check fuel and decrease. Raise RAC_Incomplete when fuel becomes zero.
   --  Do nothing for negative values of Fuel.

   procedure Check_Node
     (N    :        N_Subexpr_Id;
      Ctx  : in out Context;
      Desc :        String;
      K    :        VC_Kind);

   procedure Check_List
     (L   :        Node_Lists.List;
      Ctx : in out Context;
      Msg :        String;
      K   :        VC_Kind);
   --  Check the validity of formulas L

   type Ulargest is mod 2 ** 128;
   --  The largest modular type to execute modulo operators

   procedure Iterate_Loop_Param_Spec
     (Param_Spec :        Node_Id;
      Ctx        : in out Context;
      Iteration  : access procedure (Ctx : in out Context));
   --  Iterate a loop parameter specification by calling Iteration

   function RAC_Expr
     (N   :        N_Subexpr_Id;
      Ctx : in out Context;
      Ty0 :        Entity_Id := Empty)
      return Value;
   --  Evaluate node N to a value

   function RAC_Expr_LHS
     (N   :        N_Subexpr_Id;
      Ctx : in out Context)
      return Value_Access;
   --  Evaluate node N to a value pointer for the left-hand side of an
   --  assignment.

   procedure RAC_Statement
     (N   :        N_Statement_Other_Than_Procedure_Call_Id;
      Ctx : in out Context);
   --  RAC execution of a statement N

   procedure RAC_Pragma (N : N_Pragma_Id; Ctx : in out Context);
   --  RAC execution of a pragma N

   procedure RAC_Node (N : Node_Id; Ctx : in out Context);
   --  RAC execution of node N

   procedure RAC_List (L : List_Id; Ctx : in out Context);
   --  RAC execution of list L

   procedure RAC_Decl (Decl : Node_Id; Ctx : in out Context);
   --  Add a declaration to the first scope of the context environment

   procedure RAC_Decls (Decls : List_Id; Ctx : in out Context);
   --  Add declarations to the first scope of the context environment

   function RAC_Call
     (E       :        Entity_Id;
      Args    :        List_Id;
      Ctx     : in out Context;
      Is_Main :        Boolean := False)
      return Opt_Value;
   --  RAC execution of a call to E with parameters in Scope. If Is_Main is
   --  True, the argument values are taken from the counterexample and failing
   --  preconditions trigger stuck instead of failure.

   No_Builtin : exception;
   --  Raisen when the entity is not builtin in RAC_Call_Builtin

   function RAC_Call_Builtin
     (E              : Entity_Id;
      Sc             : Scopes.Map;
      Do_Sideeffects : Boolean)
      return Opt_Value;
   --  Execute a builtin E, if it exists, or raise No_Builtin otherwise

   procedure Init_Global
     (Scope         : in out Scopes.Map;
      N             :        Node_Id;
      Use_Expr      :        Boolean;
      Default_Value :        Boolean;
      Ctx           : in out Context;
      B             :    out Binding;
      Descr         :        String);
   --  Initialize a global variable from the counterexample value, from the
   --  expression in the declaration (if Use_Expr is true), or by a default
   --  value (if Default_Value is true).

   function Param_Scope
     (E    :        Entity_Id;
      Args :        List_Id;
      Ctx  : in out Context)
      return Scopes.Map;
   --  Create a scope of parameters for a call from the associations Args

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

   function "=" (F1, F2 : Fields.Map) return Boolean is
      C2 : Fields.Cursor;
   begin
      pragma Assert (Fields.Length (F1) = Fields.Length (F2));
      for C1 in F1.Iterate loop
         C2 := F2.Find (Fields.Key (C1));

         if not Fields.Has_Element (C2)
            or else F1 (C1).all /= F2 (C2).all
         then
            return False;
         end if;
      end loop;
      return True;
   end "=";

   function "=" (M1, M2 : Values_Map.Map) return Boolean is
      C2 : Values_Map.Cursor;
   begin
      --  ??? Cannot use Values_Map."=" because cannot define "=" for Value
      --  before definition of Values_Map
      if M1.Length /= M2.Length then
         return False;
      end if;
      for C1 in M1.Iterate loop
         C2 := M2.Find (Values_Map.Key (C1));
         if not Values_Map.Has_Element (C2)
           or else M1 (C1).all /= M2 (C2).all
         then
            return False;
         end if;
      end loop;
      return True;
   end "=";

   function "=" (V1, V2 : Value) return Boolean is
     ((V1.Ty = V2.Ty)
      and then
        (case V1.Ty is
            when Ty_Enum      =>
               V1.Enum_Entity = V2.Enum_Entity,
            when Ty_Integer   =>
               V1.Integer_Content = V2.Integer_Content,
            when Ty_Record    =>
               V1.Record_Fields = V2.Record_Fields,
            when Ty_String    =>
               V1.String_Content = V2.String_Content,
            when Ty_Array     =>
               ((V1.Array_Others = null and then V2.Array_Others = null)
                or else
                (V1.Array_Others /= null and then V2.Array_Others /= null))
               and then V1.Array_Values = V2.Array_Values));

   -------------------
   -- Boolean_Value --
   -------------------

   function Boolean_Value (B : Boolean) return Value is
     (Ty          => Ty_Enum,
      Enum_Entity => (if B then Standard_True else Standard_False));

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

   --------------------------
   -- Check_Supported_Type --
   --------------------------

   procedure Check_Supported_Type (Ty : Node_Id) is
   begin
      if Has_Discriminants (Ty) then
         RAC_Unsupported ("Type has discrimants", Ty);
      end if;
      if Has_Predicates (Ty) then
         RAC_Unsupported ("Type has predicates", Ty);
      end if;
      if Has_Invariants (Ty) then
         RAC_Unsupported ("Type has invariants", Ty);
      end if;
      if Is_Class_Wide_Type (Ty) then
         RAC_Unsupported ("Type is class wide type", Ty);
      end if;
      if Has_Dynamic_Predicate_Aspect (Ty) then
         RAC_Unsupported ("Type has dynamic predicate aspect", Ty);
      end if;
      if Is_Floating_Point_Type (Ty) then
         RAC_Unsupported ("Floating point type", Ty);
      end if;
      if Ty in Array_Kind_Id
        and then not Is_String_Type (Ty) --  string has no first index
        and then
          (No (First_Index (Ty))
           or else Present (Next_Index (First_Index (Ty))))
      then
         RAC_Unsupported ("Array type with not one index", Ty);
      end if;
   end Check_Supported_Type;

   -------------------------
   -- Check_Fuel_Decrease --
   -------------------------

   procedure Check_Fuel_Decrease (Fuel : in out Integer) is
   begin
      if Fuel = 0 then
         RAC_Incomplete ("out of fuel");
      elsif Fuel > 0 then
         Fuel := Fuel - 1;
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

   procedure Check_Integer (V : Value; Ty : Entity_Id; N : Node_Id) is
   begin
      if V.Ty = Ty_Integer then
         Check_Integer (V.Integer_Content, Ty, N);
      end if;
   end Check_Integer;

   ----------------
   -- Check_List --
   ----------------

   procedure Check_List
     (L   :        Node_Lists.List;
      Ctx : in out Context;
      Msg :        String;
      K   :        VC_Kind)
   is
   begin
      for N of L loop
         Check_Node (N, Ctx, Msg, K);
      end loop;
   end Check_List;

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node
     (N    :        N_Subexpr_Id;
      Ctx  : in out Context;
      Desc :        String;
      K    :        VC_Kind)
   is
      V : Value;
   begin
      RAC_Trace ("check node " & Node_Kind'Image (Nkind (N)));
      V := RAC_Expr (N, Ctx);

      if Value_Boolean (V) then
         RAC_Info (Capitalize (Desc), "is OK", N);
      else
         RAC_Info (Capitalize (Desc), "failed", N);
         RAC_Failure (N, K);
      end if;
   end Check_Node;

   ----------
   -- Copy --
   ----------

   function Copy (F : Fields.Map) return Fields.Map is
      Res : Fields.Map := Fields.Empty;
   begin
      for C in F.Iterate loop
         Res.Insert (Fields.Key (C), new Value'(Copy (F (C).all)));
      end loop;
      return Res;
   end Copy;

   function Copy (A : Values_Map.Map) return Values_Map.Map is
      Res : Values_Map.Map := Values_Map.Empty;
   begin
      for C in A.Iterate loop
         Res.Insert (Values_Map.Key (C), new Value'(Copy (A (C).all)));
      end loop;
      return Res;
   end Copy;

   function Copy (V : Value) return Value is
     (case V.Ty is
         when Ty_Record  =>
            Record_Value (Copy (V.Record_Fields), Empty),
         when Ty_Array   =>
            Array_Value (V.Array_First, V.Array_Last,
                         Copy (V.Array_Values),
                         (if V.Array_Others = null then null
                          else new Value'(Copy (V.Array_Others.all)))),
         when Ty_Integer =>
            Integer_Value (V.Integer_Content),
         when Ty_String  =>
            String_Value (V.String_Content),
         when Ty_Enum    =>
            Enum_Value (V.Enum_Entity));

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value (Ty : Node_Id) return Value is
   begin

      --  ??? Use Default_Value or Default_Component_Value of Ty when this is
      --      specified

      if Is_Integer_Type (Ty) then
         --  0 or Ty'First
         declare
            Fst, Lst, I : Big_Integer;
            Zero        : constant Big_Integer := 0;
         begin
            Get_Integer_Type_Bounds (Ty, Fst, Lst);
            I := (if In_Range (Zero, Fst, Lst) then Zero else Fst);
            return Integer_Value (I, Ty, Empty);
         end;

      elsif Is_Character_Type (Ty) then
         --  ??? Is this the right way to make a character literal node? Why
         --  does it print as 'h'? C.f. gnat/sem_eval.adb:2823.
         return Enum_Value
           (Make_Character_Literal
              (No_Location, Name_Find, UI_From_Int (Character'Pos ('a'))));

      elsif Is_Enumeration_Type (Ty) then
         return Enum_Value (First_Literal (Ty));

      elsif Is_Array_Type (Ty) then
         declare
            Index_Ty, Comp_Ty : Entity_Id;
            Fst, Lst          : Big_Integer;
            Other             : Value_Access;
         begin
            Get_Array_Info (Ty, Index_Ty, Comp_Ty, Fst, Lst);
            Other := new Value'(Default_Value (Comp_Ty));
            return Array_Value (Fst, Lst, Values_Map.Empty, Other);
         end;

      elsif Is_Record_Type (Ty) then
         declare
            F : Fields.Map := Fields.Empty;
            E : Entity_Id := First_Component_Or_Discriminant (Ty);
         begin
            while Present (E) loop
               F.Insert (E, new Value'(Default_Value (Etype (E))));
               Next_Component_Or_Discriminant (E);
            end loop;
            return Record_Value (F, Ty);
         end;

      elsif Is_String_Type (Ty) then
         return String_Value ("");

      elsif Is_Private_Type (Ty) then
         return Default_Value (Full_View (Ty));

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

   ---------------------------
   -- Enum_Entity_To_String --
   ---------------------------

   function Enum_Entity_To_String (E : Entity_Id) return String is
   begin
      if Nkind (E) = N_Character_Literal then
         return (1 => Get_Character
           (UI_To_CC (Uint (Char_Literal_Value (E)))));
      elsif Is_Enumeration_Type (Safe_Retysp (Etype (E))) then
         return To_Upper (Get_Name_String (Chars (E)));
      else
         raise Program_Error with ("Enum_Entity_To_String");
      end if;
   end Enum_Entity_To_String;

   ----------------
   -- Enum_Value --
   ----------------

   function Enum_Value (I : Uint; Ty : Entity_Id) return Value is
      Lit : Node_Id;
   begin
      Check_Supported_Type (Ty);
      Lit := Get_Enum_Lit_From_Pos (Ty, I, No_Location);
      return
        (Ty => Ty_Enum,
         Enum_Entity =>
           (if Nkind (Lit) = N_Character_Literal then Lit else Entity (Lit)));
   end Enum_Value;

   ------------------
   -- Find_Binding --
   ------------------

   function Find_Binding
     (E   :        N_Entity_Id;
      Ctx : in out Context)
      return Binding
   is
      C : Scopes.Cursor;
      B : Binding;
   begin
      for Scope of Ctx.Env loop
         C := Scope.Find (E);

         if Scopes.Has_Element (C) then
            return Scope (C);
         end if;
      end loop;

      --  E must be a global constant without variable input (otherwise it
      --  would have been initialized in Init_Global).
      pragma Assert (if Ekind (E) = E_Constant
                     and then not Is_Access_Variable (Etype (E))
                     then not Has_Variable_Input (E));

      --  Lazily initialize globals that were not initialized by Global_Scope
      Init_Global (Ctx.Env (Ctx.Env.Last), E, True, False, Ctx, B,
                   "constant without variable input");
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

   function Flush_RAC_Return return Opt_Value is
      V : Opt_Value;
   begin
      if Exn_RAC_Return_Value = null then
         raise Program_Error with "Flush_RAC_Return";
      end if;

      V := Exn_RAC_Return_Value.all;
      Exn_RAC_Return_Value := null;
      return V;
   end Flush_RAC_Return;

   --------------------
   -- Get_Array_Info --
   --------------------

   procedure Get_Array_Info
     (Ty                :     Node_Id;
      Index_Ty, Comp_Ty : out Entity_Id;
      Fst, Lst          : out Big_Integer)
   is
   begin
      Check_Supported_Type (Ty);
      Index_Ty := Etype (First_Index (Ty));
      Comp_Ty  :=
        Component_Type
          (if Ekind (Ty) = E_Array_Subtype then Base_Type (Ty) else Ty);
      if Is_Enumeration_Type (Index_Ty) then
         Fst := 0;
         Lst := To_Big_Integer (Get_Enum_Type_Last (Index_Ty));
      else
         Get_Integer_Type_Bounds (Index_Ty, Fst, Lst);
      end if;
   end Get_Array_Info;

   -----------------------
   -- Get_Cntexmp_Value --
   -----------------------

   function Get_Cntexmp_Value
     (N       : Node_Id;
      Cntexmp : Cntexample_File_Maps.Map)
      return Opt_Value
   is
      Filename : constant String  := File_Name (Sloc (N));
      Line     : constant Integer :=
        Integer (Get_Physical_Line_Number (Sloc (N)));
      Files_C  : constant Cntexample_File_Maps.Cursor :=
        Cntexmp.Find (Filename);
   begin
      if not Cntexample_File_Maps.Has_Element (Files_C) then
         return No_Value;
      end if;

      declare
         Lines   : Cntexample_Lines renames Cntexmp (Files_C);
         Lines_C : constant Cntexample_Line_Maps.Cursor :=
           Lines.Other_Lines.Find (Line);
      begin
         if not Cntexample_Line_Maps.Has_Element (Lines_C) then
            return No_Value;
         end if;

         declare
            Elts : Cntexample_Elt_Lists.List renames
              Lines.Other_Lines (Lines_C);
         begin
            for Elt of Elts loop
               if Trim (Node_Id'Image (N), Ada.Strings.Left) = Elt.Name then
                  return Some_Value
                    (Import (Elt.Value.all, Safe_Retysp (Etype (N)), N));
               end if;
            end loop;
            return No_Value;
         end;
      end;
   end Get_Cntexmp_Value;

   ----------------
   -- Get_Bounds --
   ----------------

   procedure Get_Bounds (N : Node_Id; Low, High : out Big_Integer) is

      procedure To_Big_Integer (N : Node_Id; I : out Big_Integer);

      procedure To_Big_Integer (N : Node_Id; I : out Big_Integer) is
      begin
         --  ??? TODO Use RAC_Expr instead to evaluate N, convert to function
         if SPARK_Atree.Compile_Time_Known_Value (N) then
            I := From_Universal_Image (UI_Image (SPARK_Atree.Expr_Value (N)));
         else
            RAC_Incomplete ("Get_Bounds: unknown during compile time");
         end if;
      end To_Big_Integer;

   --  Start of processing for Get_Bounds

   begin
      To_Big_Integer (Low_Bound (N), Low);
      To_Big_Integer (High_Bound (N), High);
   end Get_Bounds;

   ------------------------
   -- Get_Enum_Type_Last --
   ------------------------

   function Get_Enum_Type_Last (Ty : Entity_Id) return Integer is
   begin
      if Ty = Standard_Character then
         return Character'Pos (Character'Last);
      else
         declare
            Res : Integer := 0;
            Lit : Node_Id;
         begin
            case Ekind (Ty) is
            when E_Enumeration_Type =>
               Lit := First (Literals (Type_Definition (Parent (Ty))));
            when E_Enumeration_Subtype =>
               Lit := Entity (Low_Bound (Scalar_Range (Ty)));
            when others =>
               RAC_Unsupported ("Get_Enum_Type_Last", Ty);
            end case;
            while Present (Lit) loop
               Lit := Next (Lit);
               Res := Res + 1;
            end loop;
            return Res;
         end;
      end if;
   end Get_Enum_Type_Last;

   -----------------------------
   -- Get_Integer_Type_Bounds --
   -----------------------------

   procedure Get_Integer_Type_Bounds
     (Ty       :     Entity_Id;
      Fst, Lst : out Big_Integer)
   is
   begin
      if Ty = Standard_Integer then
         Fst := To_Big_Integer (Integer'First);
         Lst := To_Big_Integer (Integer'Last);
      elsif Ty = Standard_Short_Integer then
         Fst := To_Big_Integer (Integer (Short_Integer'First));
         Lst := To_Big_Integer (Integer (Short_Integer'Last));
      elsif Ty = Standard_Short_Short_Integer then
         Fst := To_Big_Integer (Integer (Short_Short_Integer'First));
         Lst := To_Big_Integer (Integer (Short_Short_Integer'Last));
      elsif Ty = Standard_Long_Integer then
         Fst := From_String (Long_Integer'First'Image);
         Lst := From_String (Long_Integer'Last'Image);
      elsif Ty = Standard_Long_Long_Integer then
         Fst := From_String (Long_Long_Integer'First'Image);
         Lst := From_String (Long_Long_Integer'Last'Image);
      elsif Ty = Standard_Long_Long_Long_Integer then
         Fst := From_String (Long_Long_Long_Integer'First'Image);
         Lst := From_String (Long_Long_Long_Integer'Last'Image);
      elsif Ty in Scalar_Kind_Id then
         Get_Bounds (Scalar_Range (Ty), Fst, Lst);
      else
         RAC_Unsupported ("Get_Integer_Type_Bounds", Ty);
      end if;
   end Get_Integer_Type_Bounds;

   ---------------
   -- Get_Value --
   ---------------

   function Get_Value
     (N           :        Node_Id;
      Ex          :        Node_Id;
      Use_Default :        Boolean;
      Ctx         : in out Context;
      Origin      :    out Value_Origin)
      return Value
   is
      OV  : Opt_Value;
      Res : Value;
   begin
      OV := Get_Cntexmp_Value (N, Ctx.Cntexmp);

      if OV.Present then
         Res := OV.Content;
         Origin := From_Counterexample;
      elsif Present (Ex) then
         Res := RAC_Expr (Ex, Ctx);
         Origin := From_Expr;
      elsif Use_Default then
         Res := Default_Value (Etype (N));
         Origin := From_Type_Default;
      else
         RAC_Incomplete
           ("No counterexample value for program parameter " &
              Get_Name_String (Chars (N)) & "(" & Node_Id'Image (N) & ")");
      end if;

      RAC_Info
        ("Get " & Get_Name_String (Chars (N)) &
           " (" & Value_Origin'Image (Origin) & ")" &
           " = " & To_String (Res));
      return Res;
   end Get_Value;

   ------------
   -- Import --
   ------------

   function Import
     (V  : Cntexmp_Value;
      Ty : Entity_Id;
      N  : Node_Id)
      return Value
   is
      function Field_Value
        (E  : Entity_Id;
         Fi : Cntexmp_Value_Array.Map)
         return Value;

      procedure Import_Error (Msg : String) with No_Return;

      -----------------
      -- Field_Value --
      -----------------

      function Field_Value
        (E  : Entity_Id;
         Fi : Cntexmp_Value_Array.Map)
         return Value
      is
         K : constant String := "." & Trim (Entity_Id'Image (E), Left);
      begin
         for C in Fi.Iterate loop
            if Cntexmp_Value_Array.Key (C) = K then
               return Import (V.Fi (C).all, Etype (E), N);
            end if;
         end loop;
         Import_Error ("field value " & K & "(" & Full_Name (E) & ", "
                       & Full_Name (Ty) & ")");
      end Field_Value;

      ------------------
      -- Import_Error --
      ------------------

      procedure Import_Error  (Msg : String) is
      begin
         if Do_RAC_Info then
            Treepr.Print_Tree_Node (N);
            Write_Line (Write (To_JSON (V), Compact => False));
         end if;
         raise RAC_Unexpected_Error with
           ("counterexample value import error: " & Msg);
         --  ??? Import errors are programming errors, but should we be more
         --  defensively, by just signalling Exn_RAC_Incomplete? Then only the
         --  counterexample classification would fail, instead of dragging
         --  along all the rest.
      end Import_Error;

   --  Start of processing for Import

   begin
      Check_Supported_Type (Ty);

      if Is_Integer_Type (Ty) then
         if V.T /= Cnt_Integer then
            Import_Error ("not integer value but " & Cntexmp_Type'Image (V.T));
         end if;
         return Integer_Value (From_String (To_String (V.I)), Ty, N);

      elsif Is_Enumeration_Type (Ty) then
         case V.T is
            when Cnt_Boolean =>
               return Boolean_Value (V.Bo);
            when Cnt_Integer =>
               return Enum_Value (UI_From_String (To_String (V.I)), Ty);
            when others =>
               Import_Error ("unexpected value type for enumeration but "
                             & Cntexmp_Type'Image (V.T));
         end case;

      elsif Is_Boolean_Type (Ty) then

         if V.T /= Cnt_Boolean then
            Import_Error ("not boolean value");
         end if;

         return Boolean_Value (Boolean'Value (To_String (V.B)));

      elsif Is_Record_Type (Ty) then

         if Has_Discriminants (Ty) or else Is_Derived_Type (Ty) then
            RAC_Unsupported
              ("Import value of discrimant or derived record", N);
         end if;

         if V.T /= Cnt_Record then
            Import_Error ("not record value");
         end if;

         declare
            F : Fields.Map := Fields.Empty;
            E : Entity_Id := First_Component_Or_Discriminant (Ty);
         begin
            while Present (E) loop
               F.Insert (E, new Value'(Field_Value (E, V.Fi)));
               Next_Component_Or_Discriminant (E);
            end loop;
            --  ??? TODO Check that all fields have values, or fill with
            --      default values
            return Record_Value (F, Ty);
         end;

      elsif Is_String_Type (Ty) then
         RAC_Unsupported ("Import of string values", N);

      elsif Is_Array_Type (Ty) then

         if V.T /= Cnt_Array then
            Import_Error ("not array value");
         end if;

         declare
            Index_Ty, Comp_Ty : Entity_Id;
            Values            : Values_Map.Map := Values_Map.Empty;
            Other             : Value_Access;
            Fst, Lst          : Big_Integer;
         begin
            Get_Array_Info (Ty, Index_Ty, Comp_Ty, Fst, Lst);
            pragma Assert (Is_Integer_Type (Index_Ty)
                            or else Is_Enumeration_Type (Index_Ty));

            for C in V.Array_Indices.Iterate loop
               declare
                  Key : Integer;
                  Val : Value;
               begin
                  Key := Integer'Value (Cntexmp_Value_Array.Key (C));
                  if not (Fst <= To_Big_Integer (Key)
                           and then To_Big_Integer (Key) <= Lst)
                  then
                     RAC_Stuck ("counterexample array index out of scope");
                  end if;
                  Val :=
                    Import (V.Array_Indices (C).all, Safe_Retysp (Comp_Ty), N);
                  Values.Insert (Key, new Value'(Val));
               exception
                  when Constraint_Error =>
                     RAC_Incomplete
                       ("Array index not an integer (or not in range)");
               end;
            end loop;

            Other := new Value'(Import (V.Array_Others.all, Comp_Ty, N));
            return Array_Value (Fst, Lst, Values, Other);
         end;

      else
         RAC_Unsupported
           ("Import", "counterexample value import for " &
              Get_Name_String (Chars (Ty)));
      end if;

   exception
      when Exn_RAC_Failure =>
         RAC_Stuck
           ("error in counterexample value: " &
              Description (Flush_Exn_RAC_Result.Res_VC_Kind));
   end Import;

   -----------------
   -- Init_Global --
   -----------------

   procedure Init_Global
     (Scope         : in out Scopes.Map;
      N             :        Node_Id;
      Use_Expr      :        Boolean;
      Default_Value :        Boolean;
      Ctx           : in out Context;
      B             :    out Binding;
      Descr         :        String)
   is
      Origin : Value_Origin;
      Expr   : constant Node_Id :=
        (if Use_Expr then Expression (Parent (N)) else Empty);
   begin
      B :=
        (Val    => new Value'(Get_Value (N, Expr, Default_Value, Ctx, Origin)),
         others => <>);
      Scope.Insert (N, B);
      RAC_Trace ("Initialize global " & Descr & " "
                 & Get_Name_String (Chars (N)) & " to "
                 & To_String (B.Val.all) & " " & Value_Origin'Image (Origin));
   end Init_Global;

   -------------------
   -- Integer_Value --
   -------------------

   function Integer_Value
     (I  : Big_Integer;
      Ty : Entity_Id;
      N  : Node_Id)
      return Value
   is
      Res : Big_Integer := I;
   begin
      if Is_Modular_Integer_Type (Ty) then
         if Modulus (Ty) = 0 then
            --  ??? TODO Modulus 0 for System.Address in
            --      O226-018__address/src/worker_pack__worker_init
            RAC_Unsupported ("Modular integer zero", Ty);
         end if;
         Res := Res mod From_String (UI_Image (Modulus (Ty)));
      else
         Check_Integer (I, Ty, N);
      end if;
      return (Ty => Ty_Integer, Integer_Content => Res);
   end Integer_Value;

   -----------------------------
   -- Iterate_Loop_Param_Spec --
   -----------------------------

   procedure Iterate_Loop_Param_Spec
     (Param_Spec :        Node_Id;
      Ctx        : in out Context;
      Iteration  : access procedure (Ctx : in out Context))
   is
      Def          : constant Node_Id :=
        Discrete_Subtype_Definition (Param_Spec);
      Actual_Range : constant Node_Id := Get_Range (Def);
      Low_Bnd      : constant Node_Id := Low_Bound (Actual_Range);
      Low          : constant Value := RAC_Expr (Low_Bnd, Ctx);
      High         : constant Value :=
        RAC_Expr (High_Bound (Actual_Range), Ctx);
      Id           : constant Node_Id :=
        Defining_Identifier (Param_Spec);
      Curr, Stop   : Big_Integer;
      Step         : Big_Integer := To_Big_Integer (1);
      Test         : -- Test for Curr and Stop during iteration
      access function (L, R : Valid_Big_Integer) return Boolean := "<="'Access;
      Val          : Value;
   begin
      if Present (Iterator_Filter (Param_Spec)) then
         RAC_Unsupported
           ("Iterate_Loop_Param_Spec iterator filter", Param_Spec);
      end if;
      if Etype (Low_Bnd) not in Discrete_Kind_Id then
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
      Ctx.Env.Prepend (Scopes.Empty);
      begin
         while Test (Curr, Stop) loop

            RAC_Trace ("Iterate : " & To_String (Curr));
            if Is_Integer_Type (Etype (Low_Bnd)) then
               Val := Integer_Value (Curr, Etype (Low_Bnd), Empty);
            elsif Is_Enumeration_Type (Etype (Low_Bnd)) then
               Val := Enum_Value
                 (UI_From_String (To_String (Curr)), Etype (Low_Bnd));
            end if;
            Set_Value (Ctx.Env (Ctx.Env.First), Id, new Value'(Val));
            Iteration (Ctx);
            Curr := Curr + Step;
         end loop;
      exception
         when Exn_RAC_Exit =>
            null;
      end;
      Ctx.Env.Delete_First;
   end Iterate_Loop_Param_Spec;

   -----------------
   -- Param_Scope --
   -----------------

   function Param_Scope
     (E    :        Entity_Id;
      Args :        List_Id;
      Ctx  : in out Context)
      return Scopes.Map
   is
      Res : Scopes.Map := Scopes.Empty;
      Arg : Node_Id := First (Args);
      Par : Entity_Id  := First_Formal (E);
      Val : Value_Access;
   begin
      while Present (Arg) loop
         pragma Assert (Present (Par));

         if Nkind (Arg) = N_Parameter_Association then
            RAC_Unsupported ("Param_Scope association", Arg);
         end if;

         case Formal_Kind (Ekind (Par)) is
            when E_In_Parameter =>
               Val := new Value'(Copy (RAC_Expr (Arg, Ctx)));
            when E_In_Out_Parameter | E_Out_Parameter =>
               --  pass scalars by value and copy-back out parameters is
               --  unnecessary due to SPARK anti-aliasing rules
               Val := RAC_Expr_LHS (Arg, Ctx);
         end case;

         Res.Insert (Par, (Val => Val, others => <>));
         Next (Arg);
         Next_Formal (Par);
      end loop;
      pragma Assert (No (Par));
      return Res;
   end Param_Scope;

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
     (E       :        Entity_Id;
      Args    :        List_Id;
      Ctx     : in out Context;
      Is_Main :        Boolean := False)
      return Opt_Value
   is
      function Cntexmp_Param_Scope return Scopes.Map;
      --  Create a scope of parameters from the counterexample

      procedure Rem_Stack_Height_Push (Ctx : in out Context);

      procedure Rem_Stack_Height_Pop (Ctx : in out Context);

      -------------------------
      -- Initial_Param_Scope --
      -------------------------

      function Cntexmp_Param_Scope return Scopes.Map is
         Res    : Scopes.Map := Scopes.Empty;
         Param  : Entity_Id  := First_Formal (E);
         Is_Out : Boolean;
         V      : Value;
         Origin : Value_Origin;
      begin
         while Present (Param) loop
            Is_Out := Ekind (Param) = E_Out_Parameter;
            V := Get_Value (Param, Empty, Is_Out, Ctx, Origin);
            Res.Insert (Param, (Val => new Value'(V), others => <>));
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

      procedure Rem_Stack_Height_Push (Ctx : in out Context) is
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

      procedure Rem_Stack_Height_Pop (Ctx : in out Context) is
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
      B         : Binding;
      Res       : Opt_Value;
      Sc        : Scopes.Map;

   --  Start of processing for RAC_Call

   begin
      RAC_Trace ("call " & Get_Name_String (Chars (E))
                 & " - " & Integer'Image (Ctx.Rem_Stack_Height));
      Rem_Stack_Height_Push (Ctx);

      if Is_Main then
         Sc := Cntexmp_Param_Scope;
      else
         Sc := Param_Scope (E, Args, Ctx);
      end if;

      begin
         Res := RAC_Call_Builtin (E, Sc, Ctx.Do_Sideeffects);
         Rem_Stack_Height_Pop (Ctx);
         return Res;
      exception
         when No_Builtin =>
            if No (Bodie) then
               RAC_Incomplete
                 ("No body for subprogram " & Get_Name_String (Chars (E)));
            end if;
      end;

      Collect_Old_Parts (Posts, Old_Nodes);
      if Present (Get_Pragma (E, Pragma_Contract_Cases)) then
         RAC_Unsupported ("RAC_Call pragma contract cases",
                          Get_Pragma (E, Pragma_Contract_Cases));
      end if;

      Ctx.Env.Prepend (Sc);

      --  Add old values to bindings (note that the entities of Old_Nodes are
      --  not unique)
      for N of Old_Nodes loop
         if N not in N_Has_Entity_Id or else No (Entity (N)) then
            RAC_Unsupported ("old value not entity", N);
         end if;
         B := Find_Binding (Entity (N), Ctx);
         if not B.Attrs.Contains (Snames.Name_Old) then
            B.Attrs.Insert (Snames.Name_Old, new Value'(Copy (B.Val.all)));
         end if;
      end loop;
      --  ??? Evaluate prefix expressions like F(X, Y, Z)'Old

      RAC_Decls (Declarations (Bodie), Ctx);

      --  Check preconditions and get stuck in main functions
      begin
         Check_List (Pres, Ctx, "Precondition", VC_Precondition);
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
            else
               raise;
            end if;
      end;

      --  Execute subprogram body
      begin
         RAC_Node (Handled_Statement_Sequence (Bodie), Ctx);
         RAC_Trace ("call terminated");
         Res := No_Value;
      exception
         when Exn_RAC_Return =>
            RAC_Trace ("call return");
            Res := Flush_RAC_Return;
      end;

      declare
         C    : Scopes.Cursor;
         B    : Boolean;
         Bind : Binding;
      begin
         --  Add result attribute for checking the postcondition
         if Res.Present then
            Bind.Attrs.Insert (Snames.Name_Result, new Value'(Res.Content));
            Ctx.Env (Ctx.Env.First).Insert (E, Bind, C, B);
         end if;

         Check_List (Posts, Ctx, "Postcondition", VC_Postcondition);

         --  Cleanup
         if Res.Present then
            Ctx.Env (Ctx.Env.First).Delete (C);
         end if;
      end;

      --  Remove old values from bindings
      for N of Old_Nodes loop
         B := Find_Binding (Entity (N), Ctx);
         B.Attrs.Exclude (Snames.Name_Old);
      end loop;

      Sc := Ctx.Env (Ctx.Env.First);
      Ctx.Env.Delete_First;

      RAC_Trace ("call result of " & Get_Name_String (Chars (E)) &
                   ": " & To_String (Res));
      Rem_Stack_Height_Pop (Ctx);
      return Res;
   end RAC_Call;

   ----------------------
   -- RAC_Call_Builtin --
   ----------------------

   function RAC_Call_Builtin
     (E              : Entity_Id;
      Sc             : Scopes.Map;
      Do_Sideeffects : Boolean)
      return Opt_Value is
   begin
      --  The implementation of Ada.Text_IO.Put_Line is just added for running
      --  the added tests TC02-027__RAC and comparing the execution with the
      --  compiled program based on the output.
      if Get_Name_String (Chars (E)) = "put_line"
        and then Present (Scope (E))
        and then Get_Name_String (Chars (Scope (E))) = "text_io"
        and then Present (Sinfo.Nodes.Scope (Scope (Sinfo.Nodes.Scope (E))))
        and then
          Get_Name_String (Chars (Scope (Sinfo.Nodes.Scope (E)))) = "ada"
      then
         if Do_Sideeffects then
            Put_Line (To_String (Sc (Sc.First).Val.String_Content));
         end if;
         return No_Value;
      else
         raise No_Builtin;
      end if;
   end RAC_Call_Builtin;

   --------------
   -- RAC_Decl --
   --------------

   procedure RAC_Decl (Decl : Node_Id; Ctx : in out Context) is
   begin
      case Nkind (Decl) is
         when N_Object_Declaration =>
            declare
               Obj_Def : Node_Id;
               V       : Value;
               Ty      : Node_Id;
            begin
               if Present (Expression (Decl)) then
                  V := RAC_Expr (Expression (Decl), Ctx);
               else
                  Obj_Def := Object_Definition (Decl);
                  if Nkind (Obj_Def) not in N_Has_Entity then
                     RAC_Unsupported
                       ("RAC_Decl with type not entity", Obj_Def);
                  end if;
                  Ty := Safe_Retysp (Etype (Obj_Def));
                  Check_Supported_Type (Ty);
                  V := Default_Value (Ty);
               end if;
               Set_Value
                 (Ctx.Env (Ctx.Env.First),
                  Defining_Identifier (Decl),
                  new Value'(V));
            end;

         when N_Pragma
            | N_Call_Marker
            | N_Full_Type_Declaration
            | N_Implicit_Label_Declaration
            | N_Freeze_Entity
            | N_Subtype_Declaration
            | N_Subprogram_Declaration
            | N_Subprogram_Specification
            | N_Subprogram_Body
         =>
            null;

         when others =>
            RAC_Unsupported ("RAC_Decl", Node_Kind'Image (Nkind (Decl)));
      end case;
   end RAC_Decl;

   ---------------
   -- RAC_Decls --
   ---------------

   procedure RAC_Decls (Decls : List_Id; Ctx : in out Context) is
      Decl : Node_Id := First (Decls);
   begin
      while Present (Decl) loop
         RAC_Decl (Decl, Ctx);
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
      Fuel           : Integer := -1;
      Stack_Height   : Integer := -1)
      return Result
   is
      function Global_Scope (Ctx : in out Context) return Scopes.Map;
      --  Prepare a scope with global variables with values from the first
      --  successful strategy:
      --  1) retrieve value from counterexample
      --  2) evaluate expression (for constant globals)
      --  3) use type default value (for write-only globals)

      ------------------
      -- Global_Scope --
      ------------------

      function Global_Scope (Ctx : in out Context) return Scopes.Map is
         Res                  : Scopes.Map := Scopes.Empty;
         Reads, Writes        : Flow_Id_Sets.Set;
         Use_Expr, Write_Only : Boolean;
         B                    : Binding;
         Scope                : constant Flow_Scope := Get_Flow_Scope (E);
      begin
         Get_Proof_Globals (E, Reads, Writes, False, Scope);

         for Id of Reads loop
            if Id.Kind in Direct_Mapping | Record_Field then
               Use_Expr := Ekind (Id.Node) = E_Constant;
               Init_Global (Res, Id.Node, Use_Expr, False, Ctx, B, "read");
            end if;
         end loop;

         for Id of Writes loop
            if
              Id.Kind in Direct_Mapping | Record_Field
              and then not Reads.Contains (Id)
            then
               Write_Only := not Reads.Contains (Id);
               Init_Global (Res, Id.Node, False, Write_Only, Ctx, B, "write");
            end if;
         end loop;

         return Res;
      end Global_Scope;

      --  Local variables

      Ctx : Context :=
        (Env              => Environments.Empty,
         Cntexmp          => Cntexmp,
         Fuel             => Fuel,
         Rem_Stack_Height => Stack_Height,
         Do_Sideeffects   => Do_Sideeffects);

   --  Start of processing for RAC_Execute

   begin
      RAC_Trace ("cntexmp: " & Write (To_JSON (Cntexmp), False));
      RAC_Trace ("entry: " & Full_Name (E));
      case Ekind (E) is
         when E_Function
            | E_Procedure
         =>
            Ctx.Env.Prepend (Global_Scope (Ctx));
            return
              (Res_Kind  => Res_Normal,
               Res_Value => RAC_Call (E, No_List, Ctx, Is_Main => True));
         when E_Package
            | E_Package_Body
            | E_Task_Type
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
     (N   :        N_Subexpr_Id;
      Ctx : in out Context;
      Ty0 :        Entity_Id := Empty)
      return Value
   is
      Ty : constant Entity_Id :=
             (if Present (Ty0) then Ty0 else Safe_Retysp (Etype (N)));

      function RAC_Aggregate return Value;

      function RAC_Attribute_Reference return Value;

      function RAC_Binary_Op return Value;

      function RAC_If_Expression return Value;

      function RAC_In return Value;

      function RAC_Op_Compare (Left, Right : Value) return Boolean;

      function RAC_Unary_Op return Value;

      -------------------
      -- RAC_Aggregate --
      -------------------

      function RAC_Aggregate return Value is
         --  ([E with delta] Ch, ... => V, ...)
         As        : Node_Id := First (Component_Associations (N));
         Ch        : Node_Id;
         V         : Value;
         Has_Exprs : constant Boolean :=
           Nkind (N) = N_Aggregate and then Present (Expressions (N));
         Fst, Lst  : Big_Integer;
         Res       : Value;
      begin

         if Nkind (N) = N_Delta_Aggregate then
            Res := RAC_Expr (Expression (N), Ctx);
         else
            if Is_Record_Type (Ty) then
               Res := Record_Value (Fields.Empty, Ty);
            else
               pragma Assert (Is_Array_Type (Ty));
               Get_Bounds (Aggregate_Bounds (N), Fst, Lst);
               Res := Array_Value (Fst, Lst, Values_Map.Empty, null);
            end if;
         end if;

         if Is_Record_Type (Ty) then
            if Has_Exprs then
               RAC_Unsupported
                 ("RAC_Expr aggregate record", "expressions");
            end if;

            while Present (As) loop
               V := RAC_Expr (Expression (As), Ctx);
               Ch := First (Choices (As));
               while Present (Ch) loop
                  if Nkind (Ch) = N_Others_Choice then
                     RAC_Unsupported
                       ("RAC_Expr aggregate", "record others");
                  end if;
                  Res.Record_Fields.Include (Entity (Ch), new Value'(V));
                  Next (Ch);
               end loop;
               Next (As);
            end loop;
            --  ??? TODO Check all values present (fill with others)

         else
            pragma Assert (Is_Array_Type (Ty));
            if
              Has_Exprs and then Present (Component_Associations (N))
            then
               RAC_Unsupported ("RAC_Expr aggregate array",
                                "expressions and associations");
            end if;

            if Has_Exprs then
               if No (Aggregate_Bounds (N)) then
                  RAC_Unsupported ("RAC_Expr aggregate array",
                                   "expressions without static bounds");
               end if;

               declare
                  Ix  : Big_Integer := Value_Enum_Integer
                    (RAC_Expr (Low_Bound (Aggregate_Bounds (N)), Ctx));
                  Hig : constant Big_Integer := Value_Enum_Integer
                    (RAC_Expr (High_Bound (Aggregate_Bounds (N)), Ctx));
                  Ex  : Node_Id := First (Expressions (N));
               begin
                  while Present (Ex) loop
                     Res.Array_Values.Include
                       (To_Integer (Ix),
                        new Value'(Copy (RAC_Expr (Ex, Ctx))));
                     Ex := Next (Ex);
                     Ix := Ix + 1;
                  end loop;
                  if Ix /= Hig + 1 then
                     RAC_Failure (N, VC_Range_Check);
                  end if;
               end;

            elsif Present (Component_Associations (N)) then
               while Present (As) loop
                  if Nkind (As) = N_Iterated_Component_Association
                    and then Present (Defining_Identifier (As))
                  then
                     RAC_Unsupported
                       ("iterated component with defining identifier", N);
                  end if;
                  if Box_Present (As) then
                     RAC_Unsupported
                       ("iterated component with box present", N);
                  end if;

                  V := RAC_Expr (Expression (As), Ctx);
                  Ch := First (Choices (As));
                  while Present (Ch) loop
                     if Nkind (Ch) = N_Range then
                        declare
                           Cur : Big_Integer := Value_Enum_Integer
                             (RAC_Expr (Low_Bound (Ch), Ctx));
                           Hig : constant Big_Integer := Value_Enum_Integer
                             (RAC_Expr (High_Bound (Ch), Ctx));
                        begin
                           while Cur <= Hig loop
                              Res.Array_Values.Include
                                (To_Integer (Cur), new Value'(Copy (V)));
                              Cur := Cur + 1;
                           end loop;
                        end;
                     else
                        case Nkind (Ch) is
                           when N_Subexpr =>
                              Res.Array_Values.Include
                                (To_Integer (Value_Enum_Integer
                                 (RAC_Expr (Ch, Ctx))),
                                 new Value'(Copy (V)));
                           when N_Others_Choice =>
                              Res.Array_Others := new Value'(Copy (V));
                           when others =>
                              RAC_Unsupported
                                ("RAC_Expr array aggregate choice", Ch);
                        end case;
                     end if;
                     Next (Ch);
                  end loop;
                  Next (As);
               end loop;
            end if;
         end if;

         return Res;
      end RAC_Aggregate;

      -----------------------------
      -- RAC_Attribute_Reference --
      -----------------------------

      function RAC_Attribute_Reference return Value is
      begin
         case Attribute_Name (N) is
            when Snames.Name_Old =>
               --  E'Old
               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
                  B : constant Binding := Find_Binding (E, Ctx);
               begin
                  return B.Attrs (Snames.Name_Old).all;
               end;

            when Snames.Name_Result =>
               --  E'Result
               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
                  B : constant Binding := Find_Binding (E, Ctx);
               begin
                  return B.Attrs (Snames.Name_Result).all;
               end;

            when Snames.Name_First
               | Snames.Name_Last
            =>
               --  T'First, T'Last
               if not Is_Integer_Type (Etype (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference first/last not integer", N);
               end if;

               declare
                  Fst, Lst : Big_Integer;
               begin
                  Get_Integer_Type_Bounds (Etype (N), Fst, Lst);

                  case Attribute_Name (N) is
                  when Snames.Name_First =>
                     return Integer_Value (Fst);
                  when Snames.Name_Last =>
                     return Integer_Value (Lst);
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
                         RAC_Expr (Ex, Ctx).Integer_Content;
                  I2 : constant Big_Integer :=
                         RAC_Expr (Next (Ex), Ctx).Integer_Content;
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
                  E   : constant Entity_Id := RAC_Expr (Ex, Ctx).Enum_Entity;
                  Ty  : constant Entity_Id := Etype (N);
                  Res : Entity_Id; -- the resulting enum literal
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

                  return Enum_Value (Res);
               end;

            when Snames.Name_Update =>
               --  Ex'Update ((Ch | ... => V, ...), ...)
               declare
                  F                : Fields.Map;
                  Ex, As, Ch       : Node_Id;
                  V                : Value;
                  FC               : Fields.Cursor;
                  Record_Not_Array : constant Boolean := Is_Record_Type (Ty);
                  Prefix_Value     : constant Value :=
                                       RAC_Expr (Prefix (N), Ctx);
               begin
                  pragma Assert (Record_Not_Array xor Is_Array_Type (Ty));
                  if Record_Not_Array then
                     F := Fields.Copy (Prefix_Value.Record_Fields);
                     Ex := First (Expressions (N));
                     while Present (Ex) loop
                        As := First (Component_Associations (Ex));
                        while Present (As) loop
                           V := RAC_Expr (Expression (As), Ctx);
                           Ch := First (Choices (As));

                           if Nkind (Ch) /= N_Identifier then
                              RAC_Unsupported
                                ("RAC_Attribute_Reference update", Ch);
                           end if;

                           while Present (Ch) loop
                              FC := F.Find (SPARK_Atree.Entity (Ch));
                              pragma Assert (Fields.Has_Element (FC));
                              F.Replace_Element (FC, new Value'(V));
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
                 (To_String (RAC_Expr (First (Expressions (N)), Ctx)));

            when Snames.Name_Length =>
               if not Is_Empty_List (Expressions (N)) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference 'Length with argument", N);
               end if;
               if not Is_String_Type (Etype (Prefix (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference 'Length prefix not string", N);
               end if;
               return Integer_Value
                 (To_Big_Integer
                    (Value_String (RAC_Expr (Prefix (N), Ctx))'Length));

            when others =>
               RAC_Unsupported
                 ("RAC_Attribute_Reference",
                  Get_Name_String (Attribute_Name (N)));
         end case;
      end RAC_Attribute_Reference;

      -------------------
      -- RAC_Binary_Op --
      -------------------

      function RAC_Binary_Op return Value is
         Left  : constant Value := RAC_Expr (Left_Opnd (N), Ctx);
         Right : constant Value := RAC_Expr (Right_Opnd (N), Ctx);
      begin
         case N_Binary_Op (Nkind (N)) is
            when N_Op_Add =>
               return
                 Integer_Value
                   (Left.Integer_Content + Right.Integer_Content, N);

            when N_Op_Expon =>
               return Integer_Value
                 (Left.Integer_Content **
                    Natural (To_Integer (Right.Integer_Content)), N);

            when N_Op_Subtract =>
               return
                 Integer_Value
                   (Left.Integer_Content - Right.Integer_Content, N);

            when N_Multiplying_Operator =>
               if Nkind (N) in N_Op_Divide | N_Op_Mod | N_Op_Rem
                 and then Right.Integer_Content = 0
               then
                  RAC_Failure (N, VC_Division_Check);
               end if;

               return
                 Integer_Value
                   ((case N_Multiplying_Operator (Nkind (N)) is
                       when N_Op_Multiply =>
                          Left.Integer_Content * Right.Integer_Content,
                       when N_Op_Divide   =>
                          Left.Integer_Content / Right.Integer_Content,
                       when N_Op_Mod      =>
                          Left.Integer_Content mod Right.Integer_Content,
                       when N_Op_Rem      =>
                          Left.Integer_Content rem Right.Integer_Content),
                    N);

            when N_Op_Boolean =>
               if Is_Boolean_Type (Etype (N)) then
                  return
                    Boolean_Value
                      (case N_Op_Boolean (Nkind (N)) is
                          when N_Op_Or  =>
                            Value_Boolean (Left) or Value_Boolean (Right),
                          when N_Op_And =>
                            Value_Boolean (Left) and Value_Boolean (Right),
                          when N_Op_Xor =>
                            Value_Boolean (Left) xor Value_Boolean (Right),
                          when others   =>
                            RAC_Op_Compare (Left, Right));

               elsif Is_Modular_Integer_Type (Etype (N)) then
                  declare
                     L : constant Ulargest :=
                           Ulargest'Value (To_String (Value_Integer (Left)));
                     R : constant Ulargest :=
                           Ulargest'Value (To_String (Value_Integer (Right)));
                     function From_Ulargest
                       (U : Ulargest) return Big_Integer is
                       (From_String (Ulargest'Image (U)));
                  begin
                     case N_Op_Boolean (Nkind (N)) is
                        when N_Op_Or  =>
                           return Integer_Value (From_Ulargest (L or R), N);
                        when N_Op_And =>
                           return Integer_Value (From_Ulargest (L and R), N);
                        when N_Op_Xor =>
                           return Integer_Value (From_Ulargest (L xor R), N);
                        when others   =>
                           return
                             Boolean_Value (RAC_Op_Compare (Left, Right));
                     end case;
                  end;

               else
                  RAC_Unsupported ("RAC_Binary_Op N_Op_Boolean", N);
               end if;

            when N_Op_Concat =>
               if Left.Ty = Ty_String and then Right.Ty = Ty_String then
                  return
                    String_Value (Value_String (Left) & Value_String (Right));
               else
                  RAC_Unsupported ("RAC_Binary_Op concat non string", N);
               end if;

            when N_Op_Shift =>
               RAC_Unsupported ("RAC_Binary_Op", N);
         end case;
      end RAC_Binary_Op;

      -----------------------
      -- RAC_If_Expression --
      -----------------------

      function RAC_If_Expression return Value is
         Cond_Expr : constant Node_Id := First (Expressions (N));
         Then_Expr : constant Node_Id := Next (Cond_Expr);
         Else_Expr : constant Node_Id := Next (Then_Expr);
      begin
         if Value_Boolean (RAC_Expr (Cond_Expr, Ctx)) then
            return RAC_Expr (Then_Expr, Ctx);
         else
            return RAC_Expr (Else_Expr, Ctx);
         end if;
      end RAC_If_Expression;

      ------------
      -- RAC_In --
      ------------

      function RAC_In return Value is
         Left_Op  : constant Node_Id := Left_Opnd (N);
         Right_Op : constant Node_Id := Right_Opnd (N);
         Left     : constant Value := RAC_Expr (Left_Op, Ctx);
         Fst, Lst, I : Big_Integer;
      begin
         if not Is_Integer_Type (Etype (Left_Op)) then
            RAC_Unsupported ("RAC_In left", Left_Opnd (N));
         end if;

         if Right_Op = Empty or else not Is_Integer_Type (Etype (Right_Op))
         then
            RAC_Unsupported ("RAC_In right not integer type", Right_Op);
         end if;

         case Nkind (Right_Op) is
            when N_Entity =>
               Get_Integer_Type_Bounds (Entity (Right_Op), Fst, Lst);
            when N_Range =>
               Fst := Value_Integer (RAC_Expr (Low_Bound (Right_Op), Ctx));
               Lst := Value_Integer (RAC_Expr (High_Bound (Right_Op), Ctx));
            when others =>
               RAC_Unsupported ("RAC_In right", Right_Op);
         end case;

         I := Left.Integer_Content;
         return Boolean_Value (Fst <= I and then I <= Lst);
      end RAC_In;

      --------------------
      -- RAC_Op_Compare --
      --------------------

      function RAC_Op_Compare (Left, Right : Value) return Boolean is
      begin
         case N_Op_Compare (Nkind (N)) is
            when N_Op_Eq =>
               return Left = Right;
            when N_Op_Ne =>
               return Left /= Right;
            when others =>
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
         end case;
      end RAC_Op_Compare;

      ------------------
      -- RAC_Unary_Op --
      ------------------

      function RAC_Unary_Op return Value is
         Right : constant Value := RAC_Expr (Right_Opnd (N), Ctx);
      begin
         case N_Unary_Op (Nkind (N)) is
            when N_Op_Abs   =>
               return Integer_Value (abs Right.Integer_Content, N);
            when N_Op_Minus =>
               return Integer_Value (-Right.Integer_Content, N);
            when N_Op_Plus  =>
               return Integer_Value (+Right.Integer_Content, N);
            when N_Op_Not   =>
               return Boolean_Value (not Value_Boolean (Right));
         end case;
      end RAC_Unary_Op;

      --  Local variables

      Res : Value;

   --  Start of processing for RAC_Expr

   begin
      RAC_Trace ("expr " & Node_Kind'Image (Nkind (N)), N);
      Check_Supported_Type (Ty);
      Check_Fuel_Decrease (Ctx.Fuel);

      if Is_Private_Type (Ty) then
         RAC_Incomplete ("expr with private type");
      end if;

      case Nkind (N) is
         when N_Integer_Literal =>
            Res :=
              Integer_Value (From_Universal_Image (UI_Image (Intval (N))), N);

         when N_Character_Literal =>
            Res := Enum_Value (N);

         when N_String_Literal =>
            Res := String_Value (Stringt.To_String (Strval (N)));

         when N_Identifier | N_Expanded_Name =>
            declare
               E : constant Entity_Id := SPARK_Atree.Entity (N);
            begin
               if Ekind (E) = E_Enumeration_Literal then
                  Res := Enum_Value (E);
               else
                  Res := Find_Binding (E, Ctx).Val.all;
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
                (Value_Boolean (RAC_Expr (Left_Opnd (N), Ctx))
                 and then
                 Value_Boolean (RAC_Expr (Right_Opnd (N), Ctx)));

         when N_Or_Else =>
            Res :=
              Boolean_Value
                (Value_Boolean (RAC_Expr (Left_Opnd (N), Ctx))
                 or else
                 Value_Boolean (RAC_Expr (Right_Opnd (N), Ctx)));

         when N_Function_Call =>
            if Nkind (Name (N)) not in N_Identifier | N_Expanded_Name then
               RAC_Unsupported ("RAC_Procedure_Call name", Name (N));
            end if;

            Res :=
              RAC_Call (Entity (Name (N)), Parameter_Associations (N), Ctx)
                .Content;

         when N_In =>
            Res := RAC_In;

         when N_If_Expression =>
            Res := RAC_If_Expression;

         when N_Qualified_Expression =>
            Res := RAC_Expr (Expression (N), Ctx, Entity (Subtype_Mark (N)));

         when N_Type_Conversion =>
            if Is_Record_Type (Entity (Subtype_Mark (N))) then
               RAC_Unsupported ("Type conversion between record types", N);
            end if;
            Res := RAC_Expr (Expression (N), Ctx, Entity (Subtype_Mark (N)));

         when N_Aggregate | N_Delta_Aggregate =>
            Res := RAC_Aggregate;

         when N_Selected_Component =>
            Res :=
              RAC_Expr (Prefix (N), Ctx).Record_Fields
                (Entity (Selector_Name (N))).all;

         when N_Indexed_Component =>
            declare
               A : constant Value := RAC_Expr (Prefix (N), Ctx);
               E : constant Node_Id := First (Expressions (N));
               V : constant Value := RAC_Expr (E, Ctx);
               I : constant Big_Integer :=  Value_Enum_Integer (V);
               C : constant Values_Map.Cursor :=
                     A.Array_Values.Find (To_Integer (I));
            begin
               if Present (Next (E)) then
                  RAC_Unsupported
                    ("RAC_Expr indexed component with many indices", N);
               end if;

               if not (A.Array_First <= I and then I <= A.Array_Last) then
                  --  ??? The index check VC is generated for the first expr
                  RAC_Failure (E, VC_Index_Check);
               end if;

               if Values_Map.Has_Element (C) then
                  Res := A.Array_Values (C).all;
               else
                  Res := Copy (A.Array_Others.all);
               end if;
            end;

         when N_Quantified_Expression =>
            declare
               Break : exception;
               procedure Iteration (Ctx : in out Context);
               procedure Iteration (Ctx : in out Context) is
                  B : constant Boolean :=
                        Value_Boolean (RAC_Expr (Condition (N), Ctx));
               begin
                  if All_Present (N) xor B then
                     raise Break;
                  end if;
               end Iteration;
            begin
               if Present (Loop_Parameter_Specification (N)) then
                  begin
                     Iterate_Loop_Param_Spec
                       (Loop_Parameter_Specification (N),
                        Ctx, Iteration'Access);
                     Res := Boolean_Value (All_Present (N));
                  exception
                     when Break =>
                        Res := Boolean_Value (not (All_Present (N)));
                  end;
               else
                  pragma Assert (Present (Iterator_Specification (N)));
                  RAC_Unsupported ("RAC_Expr quantified expression", N);
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

   function RAC_Expr_LHS
     (N   :        N_Subexpr_Id;
      Ctx : in out Context)
      return Value_Access
   is
   begin
      RAC_Trace ("expr lhs " & Node_Kind'Image (Nkind (N)), N);
      case Nkind (N) is
         when N_Identifier =>
            return Find_Binding (SPARK_Atree.Entity (N), Ctx).Val;

         when N_Type_Conversion =>
            return RAC_Expr_LHS (Expression (N), Ctx);

         when N_Selected_Component =>
            return
              RAC_Expr_LHS (Prefix (N), Ctx).all.Record_Fields
                (Entity (Selector_Name (N)));

         when N_Indexed_Component =>
            declare
               A : constant Value_Access := RAC_Expr_LHS (Prefix (N), Ctx);
               E : constant Node_Id := First (Expressions (N));
               V : constant Value := RAC_Expr (E, Ctx);
               I : constant Big_Integer := Value_Enum_Integer (V);
               C : Values_Map.Cursor := A.Array_Values.Find (To_Integer (I));
               B : Boolean;
            begin
               if Present (Next (E)) then
                  RAC_Unsupported
                    ("RAC_Expr indexed component with many indices", N);
               end if;

               if not (A.all.Array_First <= I
                        and then I <= A.all.Array_Last)
               then
                  --  ??? The index check VC is generated for the first expr
                  RAC_Failure (E, VC_Index_Check);
               end if;

               if not Values_Map.Has_Element (C) then
                  A.Array_Values.Insert
                    (To_Integer (I),
                     new Value'(Copy (A.Array_Others.all)),
                     C,
                     B);
               end if;

               return A.Array_Values (C);
            end;

         when others =>
            RAC_Unsupported ("RAC_Expr_LHS", N);
      end case;
      return null;
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

   procedure RAC_List (L : List_Id; Ctx : in out Context) is
      N : Node_Id := First (L);
   begin
      while Present (N) loop
         RAC_Node (N, Ctx);
         Next (N);
      end loop;
   end RAC_List;

   --------------
   -- RAC_Node --
   --------------

   procedure RAC_Node (N : Node_Id; Ctx : in out Context) is
      Ignore : Opt_Value;
   begin
      RAC_Trace ("node " & Node_Kind'Image (Nkind (N)), N);
      Check_Fuel_Decrease (Ctx.Fuel);

      if Nkind (N) not in N_Ignored_In_SPARK then
         case Nkind (N) is
         when N_Handled_Sequence_Of_Statements =>
            if Present (Exception_Handlers (N)) then
               RAC_Unsupported ("RAC_Node exception handler", N);
            end if;
            RAC_List (Statements (N), Ctx);
         when N_Procedure_Call_Statement =>
            Ignore :=
              RAC_Call (Entity (Name (N)), Parameter_Associations (N), Ctx);
         when N_Statement_Other_Than_Procedure_Call =>
            RAC_Statement (N, Ctx);
         when N_Pragma =>
            RAC_Pragma (N, Ctx);
         when others =>
            RAC_Unsupported ("RAC_Node", N);
         end case;
      end if;
   end RAC_Node;

   ----------------
   -- RAC_Pragma --
   ----------------

   procedure RAC_Pragma (N : N_Pragma_Id; Ctx : in out Context) is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (N));
      Desc : constant String :=
        Get_Name_String (Chars (Pragma_Identifier (N)));
   begin
      case Get_Pragma_Id (Pragma_Name (N)) is
         when Pragma_Check =>
            Check_Node (Expression (Next (Arg1)), Ctx, Desc, VC_Assert);
         when others =>
            RAC_Unsupported ("RAC_Pragma", N);
      end case;
   end RAC_Pragma;

   ----------------
   -- RAC_Return --
   ----------------

   procedure RAC_Return (V : Opt_Value) is
   begin
      Exn_RAC_Return_Value := new Opt_Value'(V);
      raise Exn_RAC_Return;
   end RAC_Return;

   -------------------
   -- RAC_Statement --
   -------------------

   procedure RAC_Statement
     (N   :        N_Statement_Other_Than_Procedure_Call_Id;
      Ctx : in out Context)
   is
   begin
      case Nkind (N) is
         when N_Null_Statement =>
            null;

         when N_Simple_Return_Statement =>
            if Present (Expression (N)) then
               declare
                  Ty  : constant Type_Kind_Id :=
                    Safe_Retysp (Etype (Return_Applies_To
                                 (Return_Statement_Entity (N))));
                  Res : constant Value :=
                    Copy (RAC_Expr (Expression (N), Ctx, Ty));
               begin
                  RAC_Return (Some_Value (Res));
               end;
            else
               RAC_Return (No_Value);
            end if;

         when N_Assignment_Statement =>
            declare
               Ty  : constant Entity_Id := Safe_Retysp (Etype (Name (N)));
               RHS : constant Value_Access :=
                 new Value'(Copy (RAC_Expr (Expression (N), Ctx, Ty)));
            begin
               case Nkind (Name (N)) is
                  when N_Identifier =>
                     Update_Value (Ctx.Env, Entity (Name (N)), RHS);

                  when N_Selected_Component =>
                     declare
                        LHS : constant Value_Access :=
                          RAC_Expr_LHS (Prefix (Name (N)), Ctx);
                        E   : constant Entity_Id :=
                          Entity (Selector_Name (Name (N)));
                     begin
                        LHS.all.Record_Fields.Include (E, RHS);
                     end;

                  when N_Indexed_Component =>
                     declare
                        LHS  : constant Value_Access :=
                          RAC_Expr_LHS (Prefix (Name (N)), Ctx);
                        Expr : constant Node_Id :=
                          First (Expressions (Name (N)));
                        V    : constant Value := RAC_Expr (Expr, Ctx);
                     begin
                        if Present (Next (Expr)) then
                           RAC_Unsupported
                             ("RAC_Expr assignment", "many indices");
                        end if;

                        LHS.all.Array_Values.Include
                          (To_Integer (Value_Enum_Integer (V)), RHS);
                     end;

                  when others =>
                     RAC_Unsupported ("N_Assignment_Statement", Name (N));
               end case;
            end;

         when N_If_Statement =>
            if Value_Boolean (RAC_Expr (Condition (N), Ctx)) then
               RAC_List (Then_Statements (N), Ctx);
            else
               declare
                  Elsif_Part : Node_Id := First (Elsif_Parts (N));
                  In_Elsif   : Boolean := False;
               begin
                  while Present (Elsif_Part) loop
                     if Value_Boolean (RAC_Expr (Condition (Elsif_Part), Ctx))
                     then
                        RAC_List (Then_Statements (Elsif_Part), Ctx);
                        In_Elsif := True;
                        exit;
                     end if;
                     Next (Elsif_Part);
                  end loop;

                  if not In_Elsif and then Present (Else_Statements (N)) then
                     RAC_List (Else_Statements (N), Ctx);
                  end if;
               end;
            end if;

         when N_Loop_Statement =>
            declare
               Scheme : constant Node_Id := Iteration_Scheme (N);
            begin
               if not Present (Scheme) then
                  begin
                     loop
                        RAC_List (Statements (N), Ctx);
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;

               elsif Present (Condition (Scheme)) then
                  --  while Condition loop Statements end loop;
                  begin
                     while
                       Value_Boolean (RAC_Expr (Condition (Scheme), Ctx))
                     loop
                        RAC_List (Statements (N), Ctx);
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;

               elsif Present (Loop_Parameter_Specification (Scheme)) then
                  declare
                     procedure Iteration (Ctx : in out Context);
                     procedure Iteration (Ctx : in out Context) is
                     begin
                        RAC_List (Statements (N), Ctx);
                     end Iteration;
                  begin
                     Iterate_Loop_Param_Spec
                       (Loop_Parameter_Specification (Scheme),
                        Ctx, Iteration'Access);
                  end;
               else
                  pragma Assert (Present (Iterator_Specification (Scheme)));
                  RAC_Unsupported ("RAC_Statement loop iterator", N);
               end if;
            end;

         when N_Exit_Statement =>
            if Present (Name (N)) then
               RAC_Unsupported ("RAC_Statement exit statement with name", N);
            end if;

            if not Present (Condition (N))
              or else Value_Boolean (RAC_Expr (Condition (N), Ctx))
            then
               raise Exn_RAC_Exit;
            end if;

         when N_Block_Statement =>
            Ctx.Env.Prepend (Scopes.Empty);
            RAC_Decls (Declarations (N), Ctx);
            RAC_Node (Handled_Statement_Sequence (N), Ctx);
            Ctx.Env.Delete_First;

         when N_Case_Statement =>
            declare
               V     : constant Value := RAC_Expr (Expression (N), Ctx);
               A     : Node_Id := First (Alternatives (N));
               Ch    : Node_Id;
               Match : Boolean;
            begin
               Outer :
               while Present (A) loop
                  Match := False;
                  Ch := First (Discrete_Choices (A));
                  while Present (Ch) loop
                     if Nkind (Ch) = N_Others_Choice then
                        Match := True;
                     elsif Nkind (Ch) in N_Subexpr then
                        if
                          Ch in N_Has_Entity_Id and then
                          Entity (Ch) in Type_Kind_Id
                        then
                           RAC_Unsupported ("case choise type", Ch);
                        end if;
                        Match := V = RAC_Expr (Ch, Ctx);
                     else
                        RAC_Unsupported ("RAC_Statement choice", Ch);
                     end if;

                     if Match then
                        RAC_List (Statements (A), Ctx);
                        exit Outer;
                     end if;

                     Next (Ch);
                  end loop;
                  Next (A);
               end loop Outer;
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
         Append (Str1, ":");
         Append (Str1, Physical_Line_Number'Image
                 (Get_Physical_Line_Number (Sloc (N))));
      end if;

      RAC_Unsupported (Str, To_String (Str1));
   end RAC_Unsupported;

   ------------------
   -- Record_Value --
   ------------------

   function Record_Value (F : Fields.Map; Ty : Entity_Id) return Value is
   begin
      if Present (Ty) then
         Check_Supported_Type (Ty);
      end if;
      return (Ty => Ty_Record, Record_Fields => F);
   end Record_Value;

   ---------------
   -- Set_Value --
   ---------------

   procedure Set_Value
     (S : in out Scopes.Map;
      E :        N_Defining_Identifier_Id;
      V :        Value_Access)
   is
      Bin : constant Binding := (Val => V, others => <>);
      C   : Scopes.Cursor;
      Ins : Boolean;
   begin
      S.Insert (E, Bin, C, Ins);

      if not Ins then
         S (C).Val := V;
      end if;
   end Set_Value;

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

   function To_String (F : Fields.Map) return String is
      Res : Unbounded_String;
      C   : Fields.Cursor := F.First;
   begin
      while Fields.Has_Element (C) loop
         Append (Res, Get_Name_String (Chars (Fields.Key (C)))
                 & " = " & To_String (F (C).all));
         Fields.Next (C);
         if Fields.Has_Element (C) then
            Append (Res, ", ");
         end if;
      end loop;
      return To_String ("(" & Res & ")");
   end To_String;

   function To_String
     (Fst, Lst : Big_Integer;
      M        : Values_Map.Map;
      O        : Value_Access)
      return String
   is
      Res : Unbounded_String;
   begin
      Append (Res, To_String (Fst) & " - " & To_String (Lst) & ",");
      for C in M.Iterate loop
         Append (Res, " "
                 & Integer'Image (Values_Map.Key (C)) & " => "
                 & To_String (M (C).all) & ",");
      end loop;
      Append (Res, " others => " &
              (if O = null then "UNDEFINED" else To_String (O.all)));
      return To_String ("(" & Res & ")");
   end To_String;

   function To_String (V : Value) return String is
     (case V.Ty is
         when Ty_Enum    => Enum_Entity_To_String (V.Enum_Entity),
         when Ty_Integer => To_String (V.Integer_Content),
         when Ty_Record  => To_String (V.Record_Fields),
         when Ty_Array   => To_String
           (V.Array_First, V.Array_Last, V.Array_Values, V.Array_Others),
         when Ty_String  => To_String (V.String_Content));

   function To_String (V : Opt_Value) return String is
     (if V.Present then To_String (V.Content) else "NONE");

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

   function To_String (Attrs : Attributes.Map) return String is
      Res : Unbounded_String;
   begin
      for C in Attrs.Iterate loop
         Append (Res, " '" & Get_Name_String (Attributes.Key (C)));
         Append (Res, "=" & To_String (Attrs (C).all));
      end loop;
      return To_String (Res);
   end To_String;

   function To_String (B : Binding) return String is
     ((if B.Val = null then "NULL" else To_String (B.Val.all))
      & " - " & To_String (B.Attrs.all));

   function To_String (S : Scopes.Map) return String is
      Res   : Unbounded_String;
      First : Boolean := True;
   begin
      for C in S.Iterate loop
         if not First then
            Append (Res, ", ");
         end if;
         Append (Res, Get_Name_String (Chars (Scopes.Key (C))));
         Append (Res, " (" & Entity_Id'Image (Scopes.Key (C)) & ")");
         Append (Res, " = " & To_String (S (C)));
         First := False;
      end loop;

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
      SC : Scopes.Cursor;
   begin
      for EC in Env.Iterate loop
         SC := Env (EC).Find (E);

         if Scopes.Has_Element (SC) then
            Env (EC) (SC).Val := V;
            return;
         end if;
      end loop;

      --  E must be a global constant without variable input (otherwise it
      --  would have been initialized in Init_Global).
      pragma Assert (if Ekind (E) = E_Constant
                     and then not Is_Access_Variable (Etype (E))
                     then not Has_Variable_Input (E));

      Env (Env.Last).Insert (E, (Val => V, others => <>));
   end Update_Value;

   -------------
   -- Boolean --
   -------------

   function Value_Boolean (V : Value) return Boolean is
   begin
      if V.Ty /= Ty_Enum then
         raise Program_Error with "Value_Boolean";
      end if;

      if V.Enum_Entity = Standard_True then
         return True;
      elsif V.Enum_Entity = Standard_False then
         return False;
      else
         raise Program_Error with "Value_Boolean";
      end if;
   end Value_Boolean;

   ------------------------
   -- Value_Enum_Integer --
   ------------------------

   function Value_Enum_Integer (V : Value) return Big_Integer is
   begin
      case V.Ty is
         when Ty_Integer =>
            return V.Integer_Content;
         when Ty_Enum =>
            return To_Big_Integer (Enum_Entity_To_Integer (V.Enum_Entity));
         when Ty_Array | Ty_Record | Ty_String =>
            raise Program_Error with "Value_Enum_Integer";
      end case;
   end Value_Enum_Integer;

   -------------------
   -- Value_Integer --
   -------------------

   function Value_Integer (V : Value) return Big_Integer is
   begin
      if V.Ty /= Ty_Integer then
         raise Program_Error with "Value_Integer";
      end if;

      return V.Integer_Content;
   end Value_Integer;

   ------------------
   -- Value_String --
   ------------------

   function Value_String (V : Value) return String is
   begin
      if V.Ty /= Ty_String then
         raise Program_Error with "Value_String";
      end if;

      return To_String (V.String_Content);
   end Value_String;

end SPARK_RAC;
