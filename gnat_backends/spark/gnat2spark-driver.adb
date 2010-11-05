------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2SPARK COMPONENTS                          --
--                                                                          --
--                    G N A T 2 S P A R K - D R I V E R                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --

-- gnat2spark is  free  software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2spark is distributed in the hope that it will  be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2spark is maintained by AdaCore (http://www.adacore.com)             --
--                                                                          --
------------------------------------------------------------------------------

with Switch;  use Switch;
with Atree;   use Atree;
with Errout;  use Errout;
with Sinfo;   use Sinfo;
with Snames;  use Snames;
with Namet;   use Namet;
with Sem_Eval; use Sem_Eval;
with Nlists;  use Nlists;

package body Gnat2SPARK.Driver is

   --   This is the main driver for the Ada-to-SPARK Back_End

   ------------------------
   -- Is_Back_End_Switch --
   ------------------------

   function Is_Back_End_Switch (Switch : String) return Boolean is
      First : constant Positive := Switch'First + 1;
      Last  : Natural           := Switch'Last;
   begin
      if Last >= First
        and then Switch (Last) = ASCII.NUL
      then
         Last := Last - 1;
      end if;

      if not Is_Switch (Switch) then
         return False;
      end if;

      --  For now we just allow the -g and -O switches, even though they
      --  will have no effect.

      case Switch (First) is
         when 'g' | 'O' =>
            return True;

         when others =>
            return False;
      end case;
   end Is_Back_End_Switch;

   -------------------
   -- GNAT_To_SPARK --
   -------------------

   procedure GNAT_To_SPARK (GNAT_Root : Node_Id) is

      type Mode is (Only_SPARK,     --  all non-SPARK features lead to errors
                    Towards_ALFA);  --  all non-ALFA features lead to errors,
                                    --  all ALFA features not in SPARK lead to
                                    --  warnings

      Cur_Mode : constant Mode := Only_SPARK;

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Exclude_Features (N : Node_Id) return Traverse_Result;
      --  Generate a message for non-ALFA features:
      --  * an error for features not in ALFA
      --  * a warning for features not yet supported, albeit in ALFA

      ----------------------
      -- Exclude_Non_ALFA --
      ----------------------

      function Exclude_Features (N : Node_Id) return Traverse_Result is

         Error_Msg_Issued : Boolean := False;

         -----------------------
         -- Local Subprograms --
         -----------------------

         procedure Error_Not_In_ALFA (Msg : String; N : Node_Id);
         --  Issue an error message saying that the feature described in Msg
         --  and related to node N is not in ALFA

         procedure Error_SPARK (Msg : String; N : Node_Id);
         --  In Only_SPARK mode, issue an error message saying that
         --  the feature described in Msg and related to node N is not in
         --  SPARK.
         --  In Towards_ALFA mode, issue a warning message saying that
         --  the feature described in Msg and related to node N is not yet in
         --  the supported subset of ALFA.

         procedure Error_Not_In_SPARK (Msg : String; N : Node_Id);
         --  Call Error_SPARK with Msg & ' not in SPARK'
         --  (e.g. 'access type not in SPARK')

         procedure Error_In_SPARK (Msg : String; N : Node_Id);
         --  Call Error_SPARK with Msg & ' in SPARK'
         --  (e.g. 'range should be static in SPARK')

         procedure Check_SPARK_Case_Statement (Stmt : Node_Id);
         --  Check that Stmt is a valid case statement in SPARK.
         --  Although SPARK has a different presentation of the grammar rules
         --  for the case statement, the same restrictions apply to Ada and
         --  SPARK, except that Ada allows 'others' as unique case alternative,
         --  SPARK does not.

         procedure Check_SPARK_Index_Constraints (Cstrs : List_Id);
         --  Check that Cstrs is a list of index constraints in SPARK

         --------------------------------
         -- Check_SPARK_Case_Statement --
         --------------------------------

         procedure Check_SPARK_Case_Statement (Stmt : Node_Id) is
            Alts, Choices : List_Id;
            Alt, Choice   : Node_Id;
         begin
            Alts := Alternatives (Stmt);
            if List_Length (Alts) = 1 then
               Alt     := First (Alts);
               Choices := Discrete_Choices (Alt);
               Choice  := First (Choices);
               case Nkind (Choice) is
                  when N_Others_Choice =>
                     Error_Not_In_SPARK
                       ("OTHERS as unique case alternative", Choice);
                  when others =>
                     null;
               end case;
            end if;
         end Check_SPARK_Case_Statement;

         -----------------------------------
         -- Check_SPARK_Index_Constraints --
         -----------------------------------

         procedure Check_SPARK_Index_Constraints (Cstrs : List_Id) is
            Cstr : Node_Id := First (Cstrs);
         begin
            while Present (Cstr) loop
               if Nkind (Cstr) = N_Discriminant_Association then
                  Error_Not_In_SPARK ("discriminant", Cstr);
               elsif Nkind (Cstr) /= N_Subtype_Indication or else
                 Present (Constraint (Cstr)) then
                  Error_In_SPARK
                    ("index constraint should be a subtype mark", Cstr);
               end if;
               Cstr := Next (Cstr);
            end loop;
         end Check_SPARK_Index_Constraints;

         -----------------------
         -- Error_Not_In_ALFA --
         -----------------------

         procedure Error_Not_In_ALFA (Msg : String; N : Node_Id) is
         begin
            Error_Msg_Issued := True;
            case Cur_Mode is
               when Only_SPARK =>
                  Error_Msg_N (Msg & " not allowed in 'S'P'A'R'K", N);
               when Towards_ALFA =>
                  Error_Msg_N (Msg & " not in 'A'L'F'A", N);
            end case;
         end Error_Not_In_ALFA;

         -----------------
         -- Error_SPARK --
         -----------------

         procedure Error_SPARK (Msg : String; N : Node_Id) is
         begin
            Error_Msg_Issued := True;
            case Cur_Mode is
               when Only_SPARK =>
                  Error_Msg_N (Msg, N);
               when Towards_ALFA =>
                  Error_Msg_N (Msg & ": not yet supported?", N);
            end case;
         end Error_SPARK;

         --------------------
         -- Error_In_SPARK --
         --------------------

         procedure Error_In_SPARK (Msg : String; N : Node_Id) is
         begin
            Error_SPARK (Msg & " in 'S'P'A'R'K", N);
         end Error_In_SPARK;

         ------------------------
         -- Error_Not_In_SPARK --
         ------------------------

         procedure Error_Not_In_SPARK (Msg : String; N : Node_Id) is
         begin
            Error_SPARK (Msg & " not allowed in 'S'P'A'R'K", N);
         end Error_Not_In_SPARK;

      begin
         case Nkind (N) is

               -----------------------------
               -- Access-related features --
               -----------------------------

            when N_Attribute_Reference =>
               if Attribute_Name (N) = Name_Access then
                  Error_Not_In_ALFA ("attribute 'Access", N);
               end if;
               --  Annex K of SPARK RM defines precisely which attributes are
               --  allowed in SPARK
               null;  --  for now

            when N_Null =>
               Error_Not_In_ALFA ("null", N);

            when N_Allocator =>
               Error_Not_In_ALFA ("allocator", N);

            when N_Incomplete_Type_Declaration =>
               Error_Not_In_ALFA ("incomplete type", N);

            when N_Explicit_Dereference =>
               Error_Not_In_ALFA ("dereference", N);

            when N_Access_To_Subprogram_Definition =>
               Error_Not_In_ALFA ("access to subprogram", N);

            when N_Free_Statement =>
               Error_Not_In_ALFA ("free statement", N);

            when N_Access_Definition
               | N_Access_To_Object_Definition =>
               Error_Not_In_ALFA ("access definition", N);

               --------------------------------
               -- Exception-related features --
               --------------------------------

            when N_Exception_Renaming_Declaration =>
               Error_Not_In_SPARK ("exception renaming", N);

            when N_Exception_Declaration =>
               Error_Not_In_ALFA ("exception declaration", N);

            when N_Exception_Handler =>
               Error_Not_In_ALFA ("exception handler", N);

               ------------------------------
               -- Generic-related features --
               ------------------------------

            when N_Formal_Object_Declaration
               | N_Formal_Type_Declaration
               | N_Formal_Subprogram_Declaration
               | N_Formal_Decimal_Fixed_Point_Definition
               | N_Formal_Derived_Type_Definition
               | N_Formal_Discrete_Type_Definition
               | N_Formal_Floating_Point_Definition
               | N_Formal_Modular_Type_Definition
               | N_Formal_Ordinary_Fixed_Point_Definition
               | N_Formal_Package_Declaration
               | N_Formal_Private_Type_Definition
               | N_Formal_Signed_Integer_Type_Definition
               =>
               Error_Not_In_SPARK ("formal generic parameter", N);

            when N_Generic_Instantiation
               | N_Generic_Association =>
               Error_Not_In_SPARK ("generic instantiation", N);

            when N_Generic_Declaration =>
               Error_Not_In_SPARK ("generic declaration", N);

            when N_Generic_Renaming_Declaration =>
               Error_Not_In_SPARK ("generic renaming", N);

               ------------------------------
               -- Tasking-related features --
               ------------------------------

            when N_Entry_Declaration
               | N_Entry_Body_Formal_Part
               | N_Entry_Body
               | N_Entry_Index_Specification =>
               Error_Not_In_ALFA ("entry", N);

            when N_Protected_Type_Declaration
               | N_Single_Protected_Declaration
               | N_Protected_Definition =>
               Error_Not_In_ALFA ("protected type", N);

            when N_Task_Type_Declaration
               | N_Task_Definition =>
               Error_Not_In_ALFA ("task type", N);

            when N_Protected_Body =>
               Error_Not_In_ALFA ("protected body", N);

            when N_Task_Body =>
               Error_Not_In_ALFA ("task body", N);

            when N_Single_Task_Declaration =>
               Error_Not_In_ALFA ("task declaration", N);

            when N_Abort_Statement =>
               Error_Not_In_ALFA ("abort statement", N);

            when N_Accept_Statement
               | N_Selective_Accept
               | N_Accept_Alternative
               | N_Delay_Alternative
               | N_Terminate_Alternative =>
               Error_Not_In_ALFA ("accept statement", N);

            when N_Asynchronous_Select
               | N_Abortable_Part
               | N_Triggering_Alternative =>
               Error_Not_In_ALFA ("asynchronous select", N);

            when N_Conditional_Entry_Call
               | N_Entry_Call_Statement
               | N_Timed_Entry_Call
               | N_Entry_Call_Alternative =>
               Error_Not_In_ALFA ("entry call", N);

            when N_Delay_Statement =>
               Error_Not_In_ALFA ("delay statement", N);

            when N_Requeue_Statement =>
               Error_Not_In_ALFA ("requeue statement", N);

               -------------------------
               -- Ada 2012 extensions --
               -------------------------

            when N_Conditional_Expression =>
               Error_Not_In_SPARK ("conditional expression", N);

            when N_Quantified_Expression =>
               Error_Not_In_SPARK ("quantified expression", N);

            when N_Case_Expression
               | N_Case_Expression_Alternative =>
               Error_Not_In_SPARK ("case expression", N);

            when N_Iterator_Specification =>
               Error_Not_In_SPARK ("iterator specification", N);

            when N_Parameterized_Expression =>
               Error_Not_In_SPARK ("parameterized expression", N);

            when N_Aspect_Specification =>
               Error_Not_In_SPARK ("aspect specification", N);

               ------------------------
               -- Non-SPARK features --
               ------------------------

            when N_Op_Abs
               | N_Op_Minus
               | N_Op_Plus =>
               --  Unary operations -, +, abs are not allowed in SPARK on
               --  modular types
               null;  --  for now

            when N_Defining_Character_Literal =>
               Error_Not_In_SPARK ("character literal in enumeration", N);

            when N_Defining_Operator_Symbol =>
               Error_Not_In_SPARK ("overloading of operations", N);

            when N_Type_Conversion =>
               --  SPARK: type conversions are limited in several ways in SPARK
               null;  --  for now

            when N_Slice =>
               Error_Not_In_SPARK ("slice", N);

            when N_Body_Stub =>
               Error_Not_In_SPARK ("body stub", N);

            when N_Use_Package_Clause =>
               Error_Not_In_SPARK ("use package clause", N);

            when N_Object_Renaming_Declaration =>
               Error_Not_In_SPARK ("object renaming", N);

            when N_Package_Renaming_Declaration =>
               --  SPARK: package renamings are restricted
               null;  --  for now

            when N_Subprogram_Renaming_Declaration =>
               --  SPARK: subprogram renamings are restricted
               null;  --  for now

            when N_Block_Statement =>
               Error_Not_In_SPARK ("block statement", N);

            when N_Case_Statement =>
               Check_SPARK_Case_Statement (N);

            when N_Loop_Parameter_Specification =>
               if Nkind (Discrete_Subtype_Definition (N)) = N_Range then
                  Error_In_SPARK
                    ("loop parameter specification should "
                       & "include subtype mark", N);
               end if;

            when N_Abstract_Subprogram_Declaration =>
               Error_Not_In_SPARK ("abstract subprogram", N);

            when N_Derived_Type_Definition =>
               if not Present (Record_Extension_Part (N)) then
                  Error_Not_In_SPARK
                    ("derived type (except record extension)", N);
               end if;

            when N_Discriminant_Association
               | N_Discriminant_Specification =>
               Error_Not_In_SPARK ("discriminant", N);

            when N_Index_Or_Discriminant_Constraint =>
               Check_SPARK_Index_Constraints (Constraints (N));

            when N_Parameter_Specification =>
               --  Although Ada RM mentions a possible 'aliased' qualifier,
               --  this is not yet defined in the RM (AI05-0142)
               if Null_Exclusion_Present (N) then
                  Error_Not_In_ALFA ("null exclusion", N);
               end if;
               if Present (Default_Expression (N)) then
                  Error_Not_In_SPARK ("default parameter expression", N);
               end if;

            when N_Range_Constraint =>
               if not Is_Static_Range (Range_Expression (N)) then
                  Error_In_SPARK ("range should be static", N);
               end if;

            when N_Variant
               | N_Variant_Part =>
               Error_Not_In_SPARK ("variant", N);

               -----------------------
               -- Non-ALFA features --
               -----------------------

            when N_Raise_xxx_Error =>
               if Comes_From_Source (N) then
                  Error_Not_In_ALFA ("raising exceptions", N);
               else
                  --  This is an exception raised by a check inserted by
                  --  the compiler:
                  --  * Constraint_Error leads to generating a VC
                  --  * Program_Error and Storage_Error are ignored
                  null;
               end if;

            when N_Binary_Op =>
               --  Binary operations may create ambiguity, depending on
               --  which operand is evaluated first, so in ALFA we should check
               --  that none of the operands writes global variables

               case N_Binary_Op'(Nkind (N)) is
               when N_Op_Concat =>
                  --  Concatenation is restricted in SPARK: it is defined only
                  --  for result type String and each operand must be either a
                  --  string literal, a static character expression, or another
                  --  concatenation.
                  null; --  for now

               when N_Op_Shift =>
                  Error_Not_In_ALFA ("bitwise shifting operations", N);

               when N_Op_Add
                  | N_Op_Expon
                  | N_Op_Subtract
                  | N_Multiplying_Operator
                  | N_Op_Compare
                  | N_Op_And
                  | N_Op_Or
                  | N_Op_Xor =>
                  null;
               end case;

            when N_Function_Call =>
               --  ALFA: only allow calls to functions which do not write
               --  globals
               null;  --  for now

            when N_Subtype_Declaration =>
               if Null_Exclusion_Present (N) then
                  Error_Not_In_ALFA ("null exclusion", N);
               end if;

            when N_Code_Statement =>
               Error_Not_In_ALFA ("code statement", N);

            when N_Goto_Statement =>
               Error_Not_In_ALFA ("goto statement", N);

            when N_Raise_Statement =>
               Error_Not_In_ALFA ("raising exceptions", N);

            when N_Extended_Return_Statement =>
               Error_Not_In_ALFA ("extended return", N);

            when N_Decimal_Fixed_Point_Definition =>
               Error_Not_In_ALFA ("decimal fixed point", N);

            when N_Delta_Constraint =>
               Error_Not_In_ALFA ("delta constraint", N);

            when N_Digits_Constraint =>
               Error_Not_In_ALFA ("digits constraint", N);

               --------------------
               -- SPARK features --
               --------------------

            when N_Defining_Identifier
               | N_Identifier
               | N_Operator_Symbol
               | N_Character_Literal
               | N_Op_Not
               | N_Membership_Test
               | N_Short_Circuit
               | N_Indexed_Component
               | N_Integer_Literal
               | N_Procedure_Call_Statement
               | N_Qualified_Expression
               | N_Aggregate
               | N_Extension_Aggregate
               | N_Range
               | N_Real_Literal
               | N_Selected_Component
               | N_String_Literal
               | N_Subtype_Indication  --  while Ada and SPARK differ in that
                                       --  only Ada allows a null exclusion on
                                       --  a subtype indication, GNAT stores
                                       --  this information in the enclosing
                                       --  declaration rather than the subtype
                                       --  indication
               | N_Component_Declaration
               | N_Full_Type_Declaration
               | N_Object_Declaration
               | N_Private_Extension_Declaration
               | N_Private_Type_Declaration
               | N_Subprogram_Specification
               | N_Unit_Body
               | N_Package_Declaration
               | N_Subprogram_Declaration
               | N_Array_Type_Definition
               | N_Assignment_Statement
               | N_Loop_Statement
               | N_Null_Statement
               | N_Simple_Return_Statement
               | N_Exit_Statement
               | N_If_Statement
               | N_Elsif_Part
               | N_Case_Statement_Alternative
               | N_Compilation_Unit
               | N_Compilation_Unit_Aux
               | N_Component_Association
               | N_Component_Definition
               | N_Component_List
               | N_Defining_Program_Unit_Name
               | N_Designator
               | N_Enumeration_Type_Definition
               | N_Floating_Point_Definition
               | N_Handled_Sequence_Of_Statements
               | N_Label
               | N_Modular_Type_Definition
               | N_Number_Declaration
               | N_Ordinary_Fixed_Point_Definition
               | N_Others_Choice
               | N_Package_Specification
               | N_Parameter_Association
               | N_Real_Range_Specification
               | N_Record_Definition
               | N_Signed_Integer_Type_Definition
               | N_Subunit
               | N_Use_Type_Clause
               | N_With_Clause
               | N_Iteration_Scheme
               =>
               null;

               -----------
               -- Other --
               -----------

            when N_Representation_Clause
               | N_Empty
               | N_Pragma_Argument_Association
               | N_Error
               | N_Expression_With_Actions
               | N_Reference
               | N_Subprogram_Info
               | N_Unchecked_Expression
               | N_Unchecked_Type_Conversion
               | N_Push_Pop_xxx_Label
               | N_Freeze_Entity
               | N_Itype_Reference
               | N_Pragma
               | N_Validate_Unchecked_Conversion
               =>
               declare
                  Kind_Str : constant String := Node_Kind'Image (Nkind (N));
               begin
                  Error_Msg_Strlen := Kind_Str'Length;
                  Error_Msg_String (1 .. Kind_Str'Length) := Kind_Str;
                  Error_Not_In_ALFA ("(not yet decided ~)", N);
               end;

            when N_Implicit_Label_Declaration
               | N_Expanded_Name  --  Should not occur in non-expanded AST?
               =>
               null;

            when N_SCIL_Dispatch_Table_Tag_Init
               | N_SCIL_Dispatching_Call
               | N_SCIL_Membership_Test
               --  Should not occur
                 =>
               pragma Assert (False);
               null;

            when N_Unused_At_Start
               | N_Unused_At_End =>
               pragma Assert (False);
               null;

         end case;

         if Error_Msg_Issued then
            return Skip;
         else
            return OK;
         end if;
      end Exclude_Features;

      procedure Traverse_ALFA is new Traverse_Proc (Exclude_Features);

   begin
      --  Treepr.Print_Node_Subtree (GNAT_Root);
      --  Sprint_Node (GNAT_Root);
      Traverse_ALFA (GNAT_Root);
   end GNAT_To_SPARK;

end Gnat2SPARK.Driver;
