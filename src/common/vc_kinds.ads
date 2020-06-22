------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                              V C _ K I N D S                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

--  This package defines the different kinds of VCs that we generate in
--  Gnat2why. The run-time checks correspond to Ada RM checks, for which the
--  front-end defines distinct constants in types.ads. Here, we use a new
--  enumeration instead of these constants, because we are only interested in
--  run-time errors that can happen in SPARK code (e.g. it excludes
--  Access_Check), and which GNATprove can detect (it excludes
--  Storage_Check), plus various assertions that we want to distinguish.

--  Changes in VC_Kind should be reflected in
--    - file gnat_expl.ml in gnatwhy3
--    - GPS plug-in spark2014.py

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Containers.Ordered_Maps;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with GNATCOLL.JSON;         use GNATCOLL.JSON;

package VC_Kinds is

   type VC_Kind is
      --  VC_RTE_Kind - run-time checks

     (VC_Division_Check,
      VC_Index_Check,
      VC_Overflow_Check,
      VC_FP_Overflow_Check,
      VC_Range_Check,
      VC_Predicate_Check,
      VC_Predicate_Check_On_Default_Value,  --  the predicate check on
                                            --  the default value of a type,
                                            --  to be used when a value of the
                                            --  type is default initialized
      VC_Null_Pointer_Dereference,
      --  This VC is to be used whenever we try to dereference an object
      --  with access type. This check should be done on the _is_null_pointer
      --  field of the why record corresponding to the pointer type.

      VC_Null_Exclusion,
      VC_Memory_Leak,
      VC_Memory_Leak_At_End_Of_Scope,

      VC_Length_Check,
      VC_Discriminant_Check,
      VC_Tag_Check,
      VC_Ceiling_Interrupt,
      VC_Initialization_Check,
      VC_Interrupt_Reserved,
      VC_Invariant_Check,
      VC_Invariant_Check_On_Default_Value,  --  the invariant check on
                                            --  the default value of a type,
                                            --  it is used once at the type
                                            --  declaration.
      VC_Ceiling_Priority_Protocol,
      VC_Task_Termination,

      --  VC_Assert_Kind - assertions

      VC_Initial_Condition,
      VC_Default_Initial_Condition,
      VC_Precondition,               --  the precondition of a call
      VC_Precondition_Main,          --  the precondition of a main program
      VC_Postcondition,              --  a postcondition
      VC_Refined_Post,               --  a refined_post
      VC_Contract_Case,
      VC_Disjoint_Contract_Cases,
      VC_Complete_Contract_Cases,
      VC_Loop_Invariant,             --  internal check kind, transformed
                                     --  by gnatwhy3 into
                                     --    VC_Loop_Invariant_Init
                                     --  or
                                     --    VC_Loop_Invariant_Preserv
      VC_Loop_Invariant_Init,
      VC_Loop_Invariant_Preserv,
      VC_Loop_Variant,
      VC_Subprogram_Variant,
      VC_Assert,
      VC_Raise,
      VC_Inline_Check,               --  Check that the Inline_For_Proof
                                     --  annotation provided for a function is
                                     --  correct.

      VC_UC_No_Holes,                --  Check that Unchecked_Conversion is
                                    --  safe from/to type
      VC_UC_Same_Size,               --  Check that the two types of an
                                    --  Unchecked_Conversion are of the same
                                    --  size

      VC_UC_Alignment,                --  Check that the two objects
                                      --  in an overlay have compatible
                                      --  alignments

      --  VC_LSP_Kind - Liskov Substitution Principle

      VC_Weaker_Pre,                  --  pre weaker than classwide pre
      VC_Trivial_Weaker_Pre,          --  specialization of VC_Weaker_Pre when
                                      --  there is no classwide or inherited
                                      --  precondition
      VC_Stronger_Post,               --  post stronger than classwide post
      VC_Weaker_Classwide_Pre,        --  classwide pre weaker than inherited
      VC_Stronger_Classwide_Post,     --  classwide post stronger t/ inherited

      VC_Weaker_Pre_Access,           --  pre of source is weaker than pre of
                                       --  target.
      VC_Stronger_Post_Access,        --  post of source is stronger than post
                                       --  of target.

      --  VC_Warning_Kind - warnings

      VC_Inconsistent_Pre,
      VC_Inconsistent_Post,
      VC_Inconsistent_Assume,
      VC_Unreachable_Branch,
      VC_Dead_Code);

   subtype VC_RTE_Kind is VC_Kind range
     VC_Division_Check .. VC_Task_Termination;

   subtype VC_Assert_Kind is VC_Kind range
     VC_Initial_Condition .. VC_UC_Alignment;

   subtype VC_LSP_Kind is VC_Kind range
     VC_Weaker_Pre .. VC_Stronger_Post_Access;

   subtype VC_Warning_Kind is VC_Kind range
     VC_Inconsistent_Pre .. VC_Dead_Code;

   type Flow_Tag_Kind is
     (Empty_Tag,
      --  Used when a tag is not specified, only for errors/warnings not checks

      Aliasing,
      --  Used for aliasing checks

      Call_In_Type_Invariant,
      --  Call to boundary program of a type from its type invariant

      Call_To_Current_Task,
      --  Call to Current_Task from invalid context

      Concurrent_Access,
      --  Global data is accessed concurrently by tasks

      Dead_Code,
      --  Statement is never reached

      Default_Initialization_Mismatch,
      --  A type marked as Fully_Default_Initialized is not fully initialized

      Depends_Missing,
      --  There is a variable missing from the RHS of a dependency

      Depends_Missing_Clause,
      --  There is an entire clause missing from the Depends contract

      Depends_Null,
      --  There is a missing dependency of the format "null => something"

      Depends_Wrong,
      --  User provided an incorrect dependency

      Export_Depends_On_Proof_In,
      --  A Proof_In variable has been used in the computation of an export

      Ghost_Wrong,
      --  A ghost procedure has a non-ghost global output

      Global_Missing,
      --  There is a variable missing from the Globals

      Global_Wrong,
      --  User provided a wrong global

      Hidden_Unexposed_State,
      --  Some hidden state has not been exposed through a state abstraction

      Illegal_Update,
      --  Writing to a variable which is not a global Output of the subprogram,
      --  or not a variable of the package during its elaboration.

      Impossible_To_Initialize_State,
      --  A state abstraction cannot possibly be initialized

      Ineffective,
      --  Code has no effect on any exports

      Initializes_Wrong,
      --  User provided an incorrect Initializes contract

      Inout_Only_Read,
      --  Inout could have been an In

      Missing_Return,
      --  Function has a path without a return statement

      Non_Volatile_Function_With_Volatile_Effects,
      --  Non Volatile_Function refers to globals with volatile effects

      Not_Constant_After_Elaboration,
      --  Variable that has been marked as Constant_After_Elaboration
      --  can potentially be updated.

      Pragma_Elaborate_All_Needed,
      --  A remote state abstraction has been used during elaboration
      --  so a pragma Elaborate_All is needed.

      Pragma_Elaborate_Body_Needed,
      --  State visible in a package spec is modified in the package
      --  elaboration.

      Potentially_Blocking_In_Protected,
      --  Protected operation calls potentially blocking feature

      Reference_To_Non_CAE_Variable,
      --  The precondition of a protected operation refers to a global
      --  variable that does not have Constant_After_Elaboration set.

      Refined_State_Wrong,
      --  User provided an incorrect Refined_State contract

      Side_Effects,
      --  A function with side-effects has been found

      Stable,
      --  Found a stable element inside a loop (this has not been
      --  implemented yet).

      Subprogram_Termination,
      --  A subprogram with annotation Terminating may not terminate

      Uninitialized,
      --  Use of an uninitialized variable

      Unused,
      --  A parameter has not been used

      Unused_Initial_Value,
      --  Initial value has not been used

      Volatile_Function_Without_Volatile_Effects
      --  Function has been marked as volatile but has no volatile effects

     );
   pragma Ordered (Flow_Tag_Kind);

   subtype Valid_Flow_Tag_Kind is Flow_Tag_Kind range
     Flow_Tag_Kind'Succ (Empty_Tag) .. Flow_Tag_Kind'Last;
   --  Non-empty tags

   subtype Data_Dependency_Tag is Flow_Tag_Kind with
     Static_Predicate => Data_Dependency_Tag in
         Global_Missing
       | Global_Wrong
       | Export_Depends_On_Proof_In
       | Illegal_Update
       | Not_Constant_After_Elaboration;
   --  Tags reported as data dependency errors

   subtype Flow_Dependency_Tag is Flow_Tag_Kind with
     Static_Predicate => Flow_Dependency_Tag in
         Depends_Null
       | Depends_Missing
       | Depends_Missing_Clause
       | Depends_Wrong
       | Initializes_Wrong;
   --  Tags reported as flow dependency errors

   function CWE_ID (Kind : VC_Kind) return String;
   function CWE_ID (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return the CWE number for a given kind as a string; return the empty
   --  string if the Kind has no associated CWE.

   function CWE_Message (Kind : VC_Kind) return String;
   function CWE_Message (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return the CWE number for a given kind as a nice string "[CWE
   --  <number>]"; return the empty string if the Kind has no associated CWE.

   function Description (Kind : VC_Kind) return String;
   function Description (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return a one-line description for each kind of message as a string

   function Kind_Name (Kind : VC_Kind) return String;
   function Kind_Name (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return a short string for each kind of message as a string, e.g. "index
   --  check" for VC_Index_Check.

   function Rule_Name (Kind : VC_Kind) return String;
   function Rule_Name (Kind : Valid_Flow_Tag_Kind) return String;
   --  Return a tag for each kind of message that is used to identify the
   --  string e.g. in the GPS plug-in.

   function Locate_On_First_Token (V : VC_Kind) return Boolean is
     (case V is when VC_RTE_Kind     => False,
                when VC_Assert_Kind  => V /= VC_Precondition,
                when VC_LSP_Kind     => True,
                when VC_Warning_Kind => True);
   --  Returns True if this kind of VC should be considered like an assertion
   --  when positioning the message to the left-most subexpression of the
   --  checked expression. For example, this is not true for VC_Precondition,
   --  which should be positioned on the location of the call.

   SPARK_Suffix : constant String := "spark";
   --  Extension of the files where spark_report expects gnat2why results

   ------------
   -- Labels --
   ------------

   --  These strings are used in Why3 labels to communicate information to
   --  Why3. Changes here should be propagated to the code of gnatwhy3. In
   --  gnat2why, use of the corresponding Name_Ids in Why.Atree.Modules is
   --  preferred over using the strings here.

   GP_Id_Marker             : constant String := "GP_Id:";
   GP_Pretty_Ada_Marker     : constant String := "GP_Pretty_Ada:";
   GP_Reason_Marker         : constant String := "GP_Reason:";
   GP_Shape_Marker          : constant String := "GP_Shape:";
   GP_Sloc_Marker           : constant String := "GP_Sloc:";
   GP_Subp_Marker           : constant String := "GP_Subp:";
   GP_Already_Proved_Marker : constant String := "GP_Already_Proved";

   --  A few labels are used in Why3 to identify variables and terms whose
   --  value is interesting in counter-examples.

   Model_Trace_Label   : constant String := "model_trace:";
   Model_Proj_Label    : constant String := "model_projected";
   VC_Annotation_Label : constant String := "vc:annotation";
   Model_VC_Post_Label : constant String := "model_vc_post";
   Branch_Id_Label     : constant String := "branch_id=";

   Model_Proj_Meta : constant String := "model_projection";
   --  A meta that is used in Why3 to mark a function as projection.

   --------------------
   --  Data Exchange --
   --------------------

   --  This section defines various types that are used to communicate between
   --  the various gnatprove processes (most notably between gnat2why/gnatwhy3
   --  and gnat2why/spark_report). Also, JSON conversion functions are defined.

   type Prover_Stat is record
      Count     : Natural;
      Max_Steps : Natural;
      Max_Time  : Float;
   end record;

   package Prover_Stat_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Prover_Stat,
                                             "<"          => "<",
                                             "="          => "=");
   --  The prover stats JSON format is defined in gnat_report.mli

   type Prover_Category is (PC_Trivial, PC_Codepeer, PC_Prover, PC_Flow);
   --  Type that describes the possible ways a check is proved. PC_Prover
   --  stands for automatic or manual proofs from Why3 and does not specify
   --  which prover proves it.
   --  PC_Trivial is used here for any "proofs" that come from gnat2why. For
   --  checks that are proved by a transformation in gnatwhy3, PC_Prover is
   --  used with a prover of name "Trivial". The distinction is necessary in
   --  some cases (e.g. to avoid redoing checks in why3). The two notions are
   --  merged by spark_report to present a single "Trivial" prover to the user.

   type CEE_Kind is (CEE_Variable,
                     CEE_Error_Msg,
                     CEE_Old,
                     CEE_Result,
                     CEE_Other);

   type Cntexmp_Type is
     (Cnt_Integer,
      Cnt_Decimal,
      Cnt_Float,
      Cnt_Boolean,
      Cnt_Bitvector,
      Cnt_Unparsed,
      Cnt_Array,
      Cnt_Record,
      Cnt_Projection,
      Cnt_Invalid);
   --  Counterexamples are typed.
   --  Matching on this types in the code should make debugging easier.
   --  Without this we would only be manipulating Unbounded_String which
   --  is not usable.

   --  Enumeration of possible float values in float counterex.
   type Float_Type is
     (Float_Plus_Infinity,
      Float_Minus_Infinity,
      Float_Plus_Zero,
      Float_Minus_Zero,
      Float_NaN,
      Float_Val);

   --  Record for float types
   type Float_Value (F_Type : Float_Type) is record
      case F_Type is
         when Float_Plus_Infinity
            | Float_Minus_Infinity
            | Float_Plus_Zero
            | Float_Minus_Zero
            | Float_NaN => null;
         when Float_Val =>
            F_Sign        : Unbounded_String;
            F_Exponent    : Unbounded_String;
            F_Significand : Unbounded_String;
      end case;
   end record;

   type Float_Value_Ptr is not null access constant Float_Value;

   type Cntexmp_Value;
   type Cntexmp_Value_Ptr is access constant Cntexmp_Value;

   package Cntexmp_Value_Array is
      new Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String, -- Indices can exceed MAX_INT
        Element_Type => Cntexmp_Value_Ptr);
   --  Map of counterexample values.
   --  In the case of counterexample array, the Key_Type represents the index.

   type Cntexmp_Value (T : Cntexmp_Type := Cnt_Invalid) is record
      case T is
         when Cnt_Integer    => I  : Unbounded_String;
         when Cnt_Decimal    => D  : Unbounded_String;
         when Cnt_Float      => F  : Float_Value_Ptr;
         when Cnt_Boolean    => Bo : Boolean;
         when Cnt_Bitvector  => B  : Unbounded_String;
         when Cnt_Unparsed   => U  : Unbounded_String;
         when Cnt_Record     =>
            Fi : Cntexmp_Value_Array.Map;
         when Cnt_Projection => Er : Unbounded_String;
            --  Cnt_projection is an error case anywhere after vc_kinds
         when Cnt_Array      =>
            Array_Indices : Cntexmp_Value_Array.Map;
            Array_Others  : Cntexmp_Value_Ptr;
         when Cnt_Invalid    => S  : Unbounded_String;
      end case;
   end record;
   --  Counterexample values
   --
   --  This record should be changed to take more precise type into account.
   --  For example, floats are actually the concatenation of two numbers "d.n"
   --  This is present in why3 and can be mimicked in SPARK.

   package S_String_List is new
     Ada.Containers.Indefinite_Doubly_Linked_Lists
       (Element_Type => Unbounded_String,
        "="          => "=");

   type CNT_Unbounded_String is record
      Nul : Boolean;
      Str : Unbounded_String;
   end record;
   --  Pair of a string for a counterexample value, and boolean Nul to denote
   --  that the string is actually for a "nul" value.

   type Cntexample_Elt is record
      Kind    : CEE_Kind;
      Name    : Unbounded_String;
      Labels  : S_String_List.List;
      Value   : Cntexmp_Value_Ptr;
      Val_Str : CNT_Unbounded_String;
   end record;

   package Cntexample_Elt_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Cntexample_Elt,
                                             "<"          => "<",
                                             "="          => "=");

   function Eq_List (A, B : Cntexample_Elt) return Boolean is
      (A.Name = B.Name);

   package Cntexample_Elt_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Element_Type => Cntexample_Elt,
                                         "="          => Eq_List);

   package Cntexample_Line_Maps is new
     Ada.Containers.Ordered_Maps (Key_Type     => Natural,
                                  Element_Type => Cntexample_Elt_Lists.List,
                                  "<"          => "<",
                                  "="          => Cntexample_Elt_Lists."=");

   type Previous_Line is record
      Line_Cnt : Cntexample_Elt_Lists.List;
      Ada_Node : Integer;  --  Node_Id of the Loop_Invariant
   end record;

   function Eq_previous (A, B : Previous_Line) return Boolean is
      (Cntexample_Elt_Lists."=" (A.Line_Cnt, B.Line_Cnt));

   package Previous_Line_Maps is new
     Ada.Containers.Ordered_Maps (Key_Type     => Natural,
                                  Element_Type => Previous_Line,
                                  "<"          => "<",
                                  "="          => Eq_previous);

   type Cntexample_Lines is record
      VC_Line        : Cntexample_Elt_Lists.List;
      --  Counterexamples on the VC line
      Other_Lines    : Cntexample_Line_Maps.Map;
      --  Counterexamples on all other lines
      Previous_Lines : Previous_Line_Maps.Map;
      --  Additional counterexamples for the previous lines
   end record;
   --  Previous lines is a feature related to loops. For Why3, intuitively, the
   --  check inside the loop assumes the loop invariant at previous iterations.
   --  So, when a counterexample appears, it contains the values at "previous
   --  iteration". These values have their locations duplicated by the VC
   --  generation exactly at the location of the while line (in Why3). So, what
   --  has been done here, is to change the location of loops to a recognizable
   --  one. These counterexamples are generated at these locations in the first
   --  pass and in the second pass (now), we recognize them to display them
   --  specially (with "Previous iteration" text).

   package Cntexample_File_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps (Key_Type     => String,
                                             Element_Type => Cntexample_Lines,
                                             "<"          => "<",
                                             "="          => "=");

   function To_String (P : Prover_Category) return String;
   --  Return a user-visible string to describe the category of prover

   function From_JSON (V : JSON_Value) return Prover_Stat;
   function From_JSON (V : JSON_Value) return Prover_Stat_Maps.Map;
   function From_JSON (V : JSON_Value) return Prover_Category;
   function From_JSON (V : JSON_Value) return Cntexample_File_Maps.Map;

   function From_JSON_Labels (Ar : JSON_Array) return S_String_List.List;

   function To_JSON (M : Prover_Stat_Maps.Map) return JSON_Value;
   function To_JSON (P : Prover_Category) return JSON_Value;
   function To_JSON (F : Cntexample_File_Maps.Map) return JSON_Value;

end VC_Kinds;
