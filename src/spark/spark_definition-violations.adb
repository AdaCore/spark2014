------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - V I O L A T I O N         --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2020-2026, AdaCore                     --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
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

with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Namet;             use Namet;
with Restrict;          use Restrict;
with Rident;            use Rident;
with Sem_Prag;          use Sem_Prag;
with Tbuild;            use Tbuild;

package body SPARK_Definition.Violations is

   function Mark_Violation_Of_SPARK_Mode return Message
   with
     Global => (Input => (Current_SPARK_Pragma, Current_Delayed_Aspect_Type));
   --  Issue an error continuation message for node N with the location of
   --  the violated SPARK_Mode pragma/aspect.

   function SRM_Reference (Kind : Violation_Kind) return String
   with
     Post =>
       SRM_Reference'Result = ""
       or else
         (SRM_Reference'Result'Length > 9
          and then Head (SRM_Reference'Result, 9) = "SPARK RM ");
   --  Return a reference to the SRM for Kind if any

   function Explain_Code (Kind : Violation_Kind) return Explain_Code_Kind;
   --  Return an explain code to be displayed along with the error message for
   --  Kind if any. If SRM_Reference
   --  is set, the reference to the SRM is appended to the error message. If
   --  Cont_Msg is set, a continuation message is issued. If Root_Cause_Msg
   --  is set, the corresponding message is used as root cause message for
   --  cascading violations (typically used if Msg has character insertions).

   function Annotation_From_Kind
     (Kind : Incorrect_Annotation_Kind) return String;
   --  Return the name of the annotation from its kind. It is used to compute
   --  the root cause for incorrect uses of annotations.

   ------------------------------
   -- Add_Violation_Root_Cause --
   ------------------------------

   procedure Add_Violation_Root_Cause (N : Node_Id; Msg : String) is
   begin
      Violation_Root_Cause.Include (N, Msg);
      Last_Violation_Root_Cause_Node := N;
   end Add_Violation_Root_Cause;

   procedure Add_Violation_Root_Cause (N : Node_Id; From : Node_Id) is
      Msg : constant String := Get_Violation_Root_Cause (From);
   begin
      if Msg /= "" then
         Add_Violation_Root_Cause (N, Msg);
      end if;
   end Add_Violation_Root_Cause;

   --------------------------
   -- Annotation_From_Kind --
   --------------------------

   function Annotation_From_Kind
     (Kind : Incorrect_Annotation_Kind) return String
   is (case Kind is
         when Annot_At_End_Borrow_Context
            | Annot_At_End_Borrow_Param
            | Annot_At_End_Borrow_Param_In_Contract         => "At_End_Borrow",
         when Annot_Handler_Call | Annot_Handler_Conversion => "Handler",
         when Annot_Hide_Info_Private_Child
            | Annot_Hide_Info_Private_Eq
            | Annot_Hide_Info_Private_Ownership             => "Hide_Info",
         when Annot_Inline_For_Proof_Body_Off               =>
           "Inline_For_Proof",
         when Annot_No_Bitwise_Operations_Use               =>
           "No_Bitwise_Operations",
         when Annot_Ownership_Potentially_Invalid           => "Ownership",
         when Annot_Predefined_Equality_Use_Eq              =>
           "Predefined_Equality");

   ------------------
   -- Explain_Code --
   ------------------

   function Explain_Code (Kind : Violation_Kind) return Explain_Code_Kind
   is (case Kind is
         when Vio_Address_Outside_Address_Clause    =>
           EC_Address_In_Expression,
         when Vio_Function_Global_Output            =>
           EC_Function_Output_Global,
         when Vio_Ownership_Borrow_Of_Non_Markable  =>
           EC_Incorrect_Source_Of_Borrow,
         when Vio_Ownership_Allocator_Uninitialized =>
           EC_Uninitialized_Allocator,
         when Vio_Side_Effects_Call_Context         =>
           EC_Call_To_Function_With_Side_Effects,
         when Vio_Volatile_At_Library_Level         =>
           EC_Volatile_At_Library_Level,
         when Vio_Volatile_Global                   =>
           EC_Function_Volatile_Input_Global,
         when Vio_Volatile_In_Interferring_Context  =>
           EC_Volatile_Non_Interfering_Context,
         when others                                => EC_None);

   -------------------------------
   -- GNATprove_Tasking_Profile --
   -------------------------------

   --  Check that the current settings match those in
   --  Sem_Prag.Set_Ravenscar_Profile.
   --  ??? Older versions of Ada are also supported to ease reuse once this
   --  code is moved to Restrict package.

   function GNATprove_Tasking_Profile return Boolean is
      function Restriction_No_Dependence (Unit : Node_Id) return Boolean;
      --  Check if restriction No_Dependence is set for Unit.

      -------------------------------
      -- Restriction_No_Dependence --
      -------------------------------

      function Restriction_No_Dependence (Unit : Node_Id) return Boolean is
         function Same_Unit (U1, U2 : Node_Id) return Boolean;
         --  Returns True iff U1 and U2 represent the same library unit.
         --  Used for handling of No_Dependence => Unit restriction case.
         --  ??? This duplicates the code from Restrict package.

         ---------------
         -- Same_Unit --
         ---------------

         function Same_Unit (U1, U2 : Node_Id) return Boolean is
         begin
            if Nkind (U1) = N_Identifier and then Nkind (U2) = N_Identifier
            then
               return Chars (U1) = Chars (U2);

            elsif Nkind (U1) in N_Selected_Component | N_Expanded_Name
              and then Nkind (U2) in N_Selected_Component | N_Expanded_Name
            then
               return
                 Same_Unit (Prefix (U1), Prefix (U2))
                 and then Same_Unit (Selector_Name (U1), Selector_Name (U2));
            else
               return False;
            end if;
         end Same_Unit;

         --  Start of processing for Restriction_No_Dependence

      begin
         --  Loop to look for entry

         for J in No_Dependences.First .. No_Dependences.Last loop

            --  Entry is in table

            if Same_Unit (Unit, No_Dependences.Table (J).Unit) then
               return True;
            end if;

         end loop;

         --  Entry is not in table

         return False;
      end Restriction_No_Dependence;

      --  Local variables

      Profile : Profile_Data renames Profile_Info (Jorvik);
      --  A minimal settings required for tasking constructs to be allowed
      --  in SPARK.

      Parent_Unit : Node_Id;
      Child_Unit  : Node_Id;
      --  For constructing names of restricted units

      --  Start of processing for GNATprove_Tasking_Profile

   begin
      if Ravenscar_Profile_Cached then
         return Ravenscar_Profile_Result;

      else
         Ravenscar_Profile_Result := True;
         Ravenscar_Profile_Cached := True;

         --  pragma Task_Dispatching_Policy (FIFO_Within_Priorities)

         if Task_Dispatching_Policy /= 'F' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Locking_Policy (Ceiling_Locking)

         if Locking_Policy /= 'C' then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         --  pragma Detect_Blocking

         if not Detect_Blocking then
            Ravenscar_Profile_Result := False;
            return False;
         end if;

         declare
            R : Restriction_Flags renames Profile.Set;
            V : Restriction_Values renames Profile.Value;
         begin
            for J in R'Range loop
               if R (J)
                 and then
                   (Restrictions.Set (J) = False
                    or else Restriction_Warnings (J)
                    or else
                      (J in All_Parameter_Restrictions
                       and then Restrictions.Value (J) > V (J)))
               then
                  --  Any code that complies with the Simple_Barriers
                  --  restriction (which is required by the Ravenscar
                  --  profile) also complies with Pure_Barriers (which is
                  --  its relaxed variant required by the Jorvik profile).

                  if J = Pure_Barriers
                    and then Restrictions.Set (Simple_Barriers)
                  then
                     null;

                  --  Likewise, No_Implicit_Task_Allocations of the Ravenscar
                  --  profile implies No_Implicit_Task_Allocations and
                  --  No_Implicit_Protected_Object_Allocations of the Jorvik
                  --  profile.

                  elsif J
                        in No_Implicit_Task_Allocations
                         | No_Implicit_Protected_Object_Allocations
                    and then Restrictions.Set (No_Implicit_Heap_Allocations)
                  then
                     null;

                  else
                     Ravenscar_Profile_Result := False;
                     return False;
                  end if;
               end if;
            end loop;
         end;

         --  The following No_Dependence restrictions:
         --    No_Dependence => Ada.Asynchronous_Task_Control
         --    No_Dependence => Ada.Task_Attributes
         --  are already checked by the above loop.

         --  The following restrictions were added to Ada 2005:
         --    No_Dependence => Ada.Execution_Time.Group_Budget
         --    No_Dependence => Ada.Execution_Time.Timers.

         if Ada_Version >= Ada_2005 then

            Parent_Unit := Sel_Comp ("ada", "execution_time", No_Location);
            Child_Unit := Sel_Comp (Parent_Unit, "group_budgets");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

            Child_Unit := Sel_Comp (Parent_Unit, "timers");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         --  The following restriction was added to Ada 2012:
         --    No_Dependence => System.Multiprocessors.Dispatching_Domains.

         if Ada_Version >= Ada_2012 then

            Parent_Unit := Sel_Comp ("system", "multiprocessors", No_Location);
            Child_Unit := Sel_Comp (Parent_Unit, "dispatching_domains");

            if not Restriction_No_Dependence (Unit => Child_Unit) then
               Ravenscar_Profile_Result := False;
               return False;
            end if;

         end if;

         return True;
      end if;
   end GNATprove_Tasking_Profile;

   ----------------------
   -- Mark_Unsupported --
   ----------------------

   procedure Mark_Incorrect_Use_Of_Annotation
     (Kind     : Incorrect_Annotation_Kind;
      N        : Node_Id;
      Msg      : String := "";
      Names    : Node_Lists.List := Node_Lists.Empty;
      Cont_Msg : String := "")
   is
      Error_Msg : constant String :=
        (if Msg /= "" then Msg else Incorrect_Annotation_Message (Kind));
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Define the root cause

      if Emit_Messages then
         Add_Violation_Root_Cause
           (N,
            Msg =>
              "incorrect use of """
              & Annotation_From_Kind (Kind)
              & """ annotation");
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Error_Msg_N
           (Create (Error_Msg, Names => Names),
            N,
            Continuations =>
              (if Cont_Msg /= "" then [Create (Cont_Msg)] else []));
      end if;
   end Mark_Incorrect_Use_Of_Annotation;

   ----------------------
   -- Mark_Unsupported --
   ----------------------

   procedure Mark_Unsupported
     (Kind     : Unsupported_Kind;
      N        : Node_Id;
      Names    : Node_Lists.List := Node_Lists.Empty;
      Name     : String := "";
      Cont_Msg : Message := No_Message)
   is
      Msg : constant String := Unsupported_Message (Kind, Name);
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Define the root cause

      if Emit_Messages then
         Add_Violation_Root_Cause
           (N, Msg => Unsupported_Message (Kind, Root_Cause => True));
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Error_Msg_N
           (Create (Msg & " is not yet supported", Names => Names),
            N,
            Continuations =>
              (if Cont_Msg /= No_Message then [Cont_Msg] else []));
      end if;
   end Mark_Unsupported;

   --------------------
   -- Mark_Violation --
   --------------------

   procedure Mark_Violation
     (Kind     : Violation_Kind;
      N        : Node_Id;
      Msg      : String := "";
      Names    : Node_Lists.List := Node_Lists.Empty;
      Cont_Msg : String := "")
   is
      SRM_Ref  : constant String := SRM_Reference (Kind);
      Code     : constant Explain_Code_Kind := Explain_Code (Kind);
      Full_Msg : Unbounded_String;
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Define the root cause. Do not use the Msg even if it is given, as it
      --  might contain references to elements in Names.

      if Emit_Messages then
         Add_Violation_Root_Cause
           (N, Msg => Violation_Message (Kind, Root_Cause => True));
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         Full_Msg :=
           To_Unbounded_String
             (if Msg /= "" then Msg else Violation_Message (Kind))
           & " is not allowed in SPARK";

         if SRM_Ref /= "" then
            Full_Msg := Full_Msg & " (" & SRM_Ref & ")";
         end if;

         declare
            Mess  : constant Message :=
              Errout_Wrapper.Create
                (To_String (Full_Msg), Names => Names, Explain_Code => Code);
            Conts : Message_Lists.List := Message_Lists.Empty;
         begin
            if Cont_Msg /= "" then
               Conts.Append (Create (Cont_Msg));
            end if;
            Conts.Append (Mark_Violation_Of_SPARK_Mode);
            Error_Msg_N (Mess, N, First => True, Continuations => Conts);
         end;
      end if;
   end Mark_Violation;

   procedure Mark_Violation
     (N : Node_Id; From : Entity_Id; Cont_Msg : String := "") is
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      --  Propagate the root cause to N if it is an entity

      if Emit_Messages then
         Add_Violation_Root_Cause (N, From);
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then
         declare
            Root_Cause : constant String := Get_Violation_Root_Cause (From);
            Root_Msg   : constant String :=
              (if Root_Cause = "" then "" else " (due to " & Root_Cause & ")");
            Conts      : Message_Lists.List := Message_Lists.Empty;
         begin
            if Cont_Msg /= "" then
               Conts.Append (Create (Cont_Msg));
            end if;
            Conts.Append (Mark_Violation_Of_SPARK_Mode);
            Error_Msg_N
              (Create
                 ("& is not allowed in SPARK" & Root_Msg, Names => [From]),
               N,
               First         => True,
               Continuations => Conts);
         end;
      end if;
   end Mark_Violation;

   -------------------------------
   -- Mark_Violation_In_Tasking --
   -------------------------------

   procedure Mark_Violation_In_Tasking (N : Node_Id) is
      Msg_Prefix : constant String := "tasking in SPARK requires ";
      Msg_Suffix : constant String := " (SPARK RM 9(2))";
   begin
      --  Flag the violation, so that the current entity is marked
      --  accordingly.

      Violation_Detected := True;

      if Emit_Messages then
         Add_Violation_Root_Cause (N, "tasking configuration");
      end if;

      --  If SPARK_Mode is On, raise an error

      if Emit_Messages and then SPARK_Pragma_Is (Opt.On) then

         if not GNATprove_Tasking_Profile then
            Error_Msg_N
              (Create (Msg_Prefix & "Ravenscar profile" & Msg_Suffix),
               N,
               First         => True,
               Continuations => [Mark_Violation_Of_SPARK_Mode]);
         elsif not Sequential_Elaboration then
            Error_Msg_N
              (Create (Msg_Prefix & "sequential elaboration" & Msg_Suffix),
               N,
               First         => True,
               Continuations => [Mark_Violation_Of_SPARK_Mode]);
         end if;
      end if;
   end Mark_Violation_In_Tasking;

   ----------------------------------
   -- Mark_Violation_Of_SPARK_Mode --
   ----------------------------------

   function Mark_Violation_Of_SPARK_Mode return Message is
   begin
      if Present (Current_SPARK_Pragma) then
         return
           Create
             ("violation of "
              & (if From_Aspect_Specification (Current_SPARK_Pragma)
                 then "aspect"
                 else "pragma")
              & " SPARK_Mode #",
              Secondary_Loc => Sloc (Current_SPARK_Pragma));
      elsif Present (Current_Incomplete_Type) then
         return
           Create
             ("access to incomplete type & is required to be in SPARK",
              Secondary_Loc => Sloc (Current_Incomplete_Type),
              Names         => [Current_Incomplete_Type]);
      else
         pragma Assert (Present (Current_Delayed_Aspect_Type));
         return
           Create
             ("delayed type aspect on & is required to be in SPARK",
              Secondary_Loc => Sloc (Current_Delayed_Aspect_Type),
              Names         => [Current_Delayed_Aspect_Type]);
      end if;
   end Mark_Violation_Of_SPARK_Mode;

   ---------------------
   -- SPARK_Pragma_Is --
   ---------------------

   function SPARK_Pragma_Is (Mode : Opt.SPARK_Mode_Type) return Boolean
   is (if Present (Current_Incomplete_Type)
         or else
           (Present (Current_Delayed_Aspect_Type)
            and then In_SPARK (Current_Delayed_Aspect_Type))
       then Mode = Opt.On
       --  Force SPARK_Mode => On for expressions of a delayed aspects, if the
       --  type bearing this aspect was marked in SPARK, as we have assumed
       --  it when marking everything between their declaration and freezing
       --  point, so we cannot revert that. Also force it for completion of
       --  incomplete types.

       elsif Present (Current_SPARK_Pragma)
       then Get_SPARK_Mode_From_Annotation (Current_SPARK_Pragma) = Mode
       --  In the usual case where Current_SPARK_Pragma is a pragma node, get
       --  the current mode from the pragma.

       --  Otherwise there is no applicable pragma, so SPARK_Mode is None

       else Mode = Opt.None);

   -------------------
   -- SRM_Reference --
   -------------------

   function SRM_Reference (Kind : Violation_Kind) return String
   is (case Kind is
         when Vio_Access_Constant
         => "SPARK RM 4.1.4(6)",
         when Vio_Access_Expression | Vio_Access_No_Root
         => "SPARK RM 4.1.4(1)",
         when Vio_Access_Function_With_Side_Effects
         => "SPARK RM 4.1.4(4)",
         when Vio_Access_Subprogram_Within_Protected
         => "SPARK RM 4.1.4(2)",
         when Vio_Access_Sub_Formal_With_Inv
            | Vio_Access_Sub_Return_Type_With_Inv
         => "SPARK RM 4.1.4(2)",
         when Vio_Access_Sub_With_Globals
         => "SPARK RM 4.1.4(7)",
         when Vio_Access_To_Dispatch_Op
         => "SPARK RM 4.1.4(2)",
         when Vio_Access_Volatile_Function
         => "SPARK RM 4.1.4(3)",
         when Vio_Address_Outside_Address_Clause
         => "SPARK RM 13.7(2)",
         when Vio_Assert_And_Cut_Context
         => "SPARK RM 5.9",
         when Vio_Backward_Goto
         => "SPARK RM 5.8(1)",
         when Vio_Box_Notation_Without_Init
         => "SPARK RM 4.3(1)",
         when Vio_Controlled_Types
         => "SPARK RM 7.6(1)",
         when Vio_Default_With_Current_Instance
         => "SPARK RM 3.8(1)",
         when Vio_Derived_Untagged_With_Tagged_Full_View
         => "SPARK RM 3.4(1)",
         when Vio_Discriminant_Access
         => "SPARK RM 3.7(2)",
         when Vio_Discriminant_Derived
         => "SPARK RM 3.7(2)",
         when Vio_Dispatch_Plain_Pre
         => "SPARK RM 6.1.1(2)",
         when Vio_Dispatching_Untagged_Type
         => "SPARK RM 3.9.2(1)",
         when Vio_Exit_Cases_Exception
         => "SPARK RM 6.1.11(3)",
         when Vio_Exit_Cases_Normal_Only
         => "SPARK RM 6.1.11(2)",
         when Vio_Function_Global_Output | Vio_Function_Out_Param
         => "SPARK RM 6.1(6)",
         when Vio_Ghost_Concurrent_Comp
         => "SPARK RM 6.9(22)",
         when Vio_Ghost_Eq
         => "SPARK RM 6.9(23)",
         when Vio_Ghost_Volatile
         => "SPARK RM 6.9(9)",
         when Vio_Handler_Choice_Parameter
         => "SPARK RM 11.2(1)",
         when Vio_Invariant_Class | Vio_Invariant_Ext | Vio_Invariant_Partial
         => "SPARK RM 7.3.2(2)",
         when Vio_Invariant_Volatile
         => "SPARK RM 7.3.2(4)",
         when Vio_Iterable_Controlling_Result
            | Vio_Iterable_Globals
            | Vio_Iterable_Side_Effects
            | Vio_Iterable_Volatile
         => "SPARK RM 5.5.2(12)",
         when Vio_Iterable_Full_View
         => "SPARK RM 5.5.2(13)",
         when Vio_Iterator_Specification
         => "SPARK RM 5.5.2",
         when Vio_Loop_Variant_Structural
         => "SPARK RM 5.5.3 (8)",
         when Vio_Overlay_Constant_Not_Imported
         => "SPARK RM 13.7(5)",
         when Vio_Overlay_Mutable_Constant
         => "SPARK RM 13.7(4)",
         when Vio_Overlay_Part_Of_Protected
         => "SPARK RM 13.7(3)",
         when Vio_Ownership_Access_Equality
         => "SPARK RM 3.10(19)",
         when Vio_Ownership_Allocator_Invalid_Context
         => "SPARK RM 4.8(2)",
         when Vio_Ownership_Allocator_Uninitialized
         => "SPARK RM 4.8(1)",
         when Vio_Ownership_Anonymous_Access_To_Named
         => "SPARK RM 3.10(18)",
         when Vio_Ownership_Anonymous_Object_Context
            | Vio_Ownership_Anonymous_Object_Init
         => "SPARK RM 3.10(5)",
         when Vio_Ownership_Assign_To_Expr | Vio_Ownership_Assign_To_Constant
         => "SPARK RM 3.10(3)",
         when Vio_Ownership_Borrow_Of_Constant
         => "SPARK RM 3.10(11)",
         when Vio_Ownership_Borrow_Of_Non_Markable
         => "SPARK RM 3.10(4)",
         when Vio_Ownership_Deallocate_General
         => "SPARK RM 3.10(20)",
         when Vio_Ownership_Loop_Entry_Old_Copy
            | Vio_Ownership_Loop_Entry_Old_Traversal
         => "SPARK RM 3.10(13)",
         when Vio_Ownership_Move_Not_Name
            | Vio_Ownership_Move_Constant_Part
            | Vio_Ownership_Move_Traversal_Call
         => "SPARK RM 3.10(1)",
         when Vio_Ownership_Reborrow
         => "SPARK RM 3.10(8)",
         when Vio_Ownership_Tagged_Extension
         => "SPARK RM 3.10(14)",
         when Vio_Ownership_Traversal_Extended_Return
         => "SPARK RM 3.10(6)",
         when Vio_Ownership_Volatile
         => "SPARK RM 3.10(16)",
         when Vio_Ownership_Anonymous_Result
            | Vio_Ownership_Anonymous_Component
            | Vio_Ownership_Anonymous_Part_Of
            | Vio_Ownership_Move_In_Declare
            | Vio_Ownership_Different_Branches
            | Vio_Ownership_Duplicate_Aggregate_Value
            | Vio_Ownership_Storage_Pool
         => "SPARK RM 3.10", --  We don't have better, use the access section
         when Vio_Potentially_Invalid_Dispatch
         => "SPARK RM 13.9.1(9)",
         when Vio_Potentially_Invalid_Invariant
         => "SPARK RM 13.9.1(7)",
         when Vio_Potentially_Invalid_Overlay
         => "SPARK RM 13.9.1(8)",
         when Vio_Potentially_Invalid_Part_Access
            | Vio_Potentially_Invalid_Part_Concurrent
            | Vio_Potentially_Invalid_Part_Tagged
            | Vio_Potentially_Invalid_Part_Unchecked_Union
         => "SPARK RM 13.9.1(5)",
         when Vio_Potentially_Invalid_Scalar
         => "SPARK RM 13.9.1(4)",
         when Vio_Program_Exit_Outputs
         => "SPARK RM 6.1.10(1)",
         when Vio_Predicate_Volatile
         => "SPARK RM 3.2.4(3)",
         when Vio_Relaxed_Init_Dispatch
         => "SPARK RM 6.10(10)",
         when Vio_Relaxed_Init_Initialized_Prefix
         => "SPARK RM 6.10(4)",
         when Vio_Relaxed_Init_Part_Of_Tagged
         => "SPARK RM 6.10(6)",
         when Vio_Relaxed_Init_Part_Of_Unchecked_Union
         => "SPARK RM 6.10(8)",
         when Vio_Relaxed_Init_Part_Of_Volatile
         => "SPARK RM 6.10(7)",
         when Vio_Side_Effects_Call_Context
         => "SPARK RM 6.1.13(4)",
         when Vio_Side_Effects_Eq
         => "SPARK RM 6.1.13(8)",
         when Vio_Side_Effects_Traversal
         => "SPARK RM 6.1.13(7)",
         when Vio_Subp_Variant_Structural
         => "SPARK RM 6.1.8(5)",
         when Vio_Tagged_Extension_Local
         => "SPARK RM 3.9.1(1)",
         when Vio_Target_Name_In_Call_With_Side_Effets
         => "SPARK RM 6.4.2(7)",
         when Vio_Tasking_Synchronized_Comp
         => "SPARK RM 9(5)",
         when Vio_Tasking_Unintialized_Concurrent
         => "SPARK RM 9(4)",
         when Vio_UC_From_Access
         => "SPARK RM 13.9(1)",
         when Vio_UC_To_Access
            | Vio_UC_To_Access_Components
            | Vio_UC_To_Access_From
         => "SPARK RM 13.9(2)",
         when Vio_Volatile_At_Library_Level
         => "SPARK RM 7.1.3(3)",
         when Vio_Volatile_Discriminant | Vio_Volatile_Loop_Param
         => "SPARK RM 7.1.3(4)",
         when Vio_Volatile_Discriminated_Type
         => "SPARK RM 7.1.3(5)",
         when Vio_Volatile_Eq
         => "SPARK RM 7.1.3(10)",
         when Vio_Volatile_Global
         => "SPARK RM 7.1.3(7)",
         when Vio_Volatile_In_Interferring_Context
         => "SPARK RM 7.1.3(9)",
         when Vio_Volatile_Incompatible_Comp
         => "SPARK RM 7.1.3(6)",
         when Vio_Volatile_Incompatible_Type
         => "SPARK RM 7.1.3(2)",
         when Vio_Volatile_Result | Vio_Volatile_Parameter
         => "SPARK RM 7.1.3(8)",
         when others
         => "");

end SPARK_Definition.Violations;
