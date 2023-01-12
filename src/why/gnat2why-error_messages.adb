------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2014-2023, AdaCore                     --
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

with Ada.Characters.Latin_1;    use Ada.Characters.Latin_1;
with Ada.Exceptions;            use Ada.Exceptions;
with Ada.Strings;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Containers.Vectors;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Float_Text_IO;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Call;                      use Call;
with CE_RAC;                    use CE_RAC;
with Common_Containers;         use Common_Containers;
with Comperr;                   use Comperr;
with Debug;                     use Debug;
with Flow_Refinement;           use Flow_Refinement;
with Flow_Types;                use Flow_Types;
with Flow_Utility;              use Flow_Utility;
with Gnat2Why.Assumptions;      use Gnat2Why.Assumptions;
with Gnat2Why.Util;             use Gnat2Why.Util;
with Gnat2Why_Args;             use Gnat2Why_Args;
with Gnat2Why_Opts;             use Gnat2Why_Opts;
with GNATCOLL.Utils;
with Osint;                     use Osint;
with Output;                    use Output;
with Sinput;                    use Sinput;
with SPARK_Atree.Entities;      use SPARK_Atree.Entities;
with Uintp;                     use Uintp;

package body Gnat2Why.Error_Messages is

   type VC_Info is record
      Node       : Node_Id;
      Kind       : VC_Kind;
      Check_Info : Check_Info_Type;
   end record;

   function Hash (X : VC_Id) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type (X));

   package Id_Tables is new Ada.Containers.Vectors
     (Index_Type   => VC_Id,
      Element_Type => VC_Info,
      "="          => "=");

   package Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => VC_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Ent_Id_Set_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Id_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Id_Sets."=");

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id);
   --  Enter the VC_Id into the map from entities to Id_Sets

   procedure Mark_VC_As_Proved_For_Entity
     (Id   : VC_Id;
      Kind : VC_Kind;
      E    : Entity_Id);
   --  Remove the VC_Id from the map from entities to Id_Sets

   procedure Mark_Subprograms_With_No_VC_As_Proved;
   --  For all subprograms that do not contain any VC, issue related claims

   function Not_Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  Return the message string for an unproved VC

   function Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  Return the message string for a proved VC

   function To_String
     (Kind : VC_Kind; Node : Node_Id) return String
   is
     (Not_Proved_Message (Node, Kind) &
        " at " & File_Name (Sloc (Node)) & ":" &
        GNATCOLL.Utils.Image
          (Positive (Get_Physical_Line_Number (Sloc (Node))), Min_Width => 0) &
        ":" &
        GNATCOLL.Utils.Image
          (Natural (Get_Column_Number (Sloc (Node))), Min_Width => 0) &
        " (" & Kind'Image & " at " &
        GNATCOLL.Utils.Image
          (Natural (Node), Min_Width => 0) &
        ")");
   --  Pretty print a VC and info for debugging

   function Decide_Cntexmp_Verdict
     (Small_Step : CE_RAC.Result;
      Giant_Step : CE_RAC.Result;
      VC         : VC_Id;
      Info       : VC_Info)
      return Cntexmp_Verdict;
   --  Categorise a proof failure based on the results from the normal and
   --  giant-step runtime-assertion checking (RAC) with the counterexample
   --  according to Figure 11 in the technical report "Giant-step Semantics for
   --  the Categorisatio of Counterexamples" (hal-03213438).

   function VC_Kinds_Match (Target_Kind, Found_Kind : VC_Kind) return Boolean
   is (Target_Kind = Found_Kind
         or else
      (Target_Kind in VC_Range_Kind and then Found_Kind in VC_Range_Kind)
         or else
      (Target_Kind in VC_Assert_Kind and then Found_Kind in VC_Assert_Kind)
         or else
      (Target_Kind in VC_Inline_Check
         and then Found_Kind in VC_Postcondition));
   --  When checking whether the VC kind by RAC matches the target VC kind,
   --  collapse all scalar checks for now, as RAC cannot distinguish with them
   --  when a node has has the Do_Range_Check flag set to True. Indeed, RAC
   --  does not have the machinery to determine what check is emitted in
   --  gnat2why for a given Do_Range_Check flag, so it uses consistently
   --  VC_Range_Check.
   --
   --  Similarly, RAC will use the generic VC_Assert for various kinds of
   --  assertions, so collapse all assertions for now.
   --
   --  If the target VC kind is VC_Inline_Check, we know that finding the
   --  triggered VC to be VC_Postcondition corresponds to the same check.
   --  Therefore it is also accepted.

   VC_Table : Id_Tables.Vector := Id_Tables.Empty_Vector;
   --  This table maps ids to their VC_Info (entity and Ada node)

   function Find_VC (N : Node_Id; Kind : VC_Kind) return VC_Id;
   --  Find the key of a VC in VC_Table

   Registered_VCs_In_Why3 : Natural := 0;

   VC_Set_Table : Ent_Id_Set_Maps.Map := Ent_Id_Set_Maps.Empty_Map;
   --  This table maps entities to the set of unproved VCs

   ----------------------
   -- Add_Id_To_Entity --
   ----------------------

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id) is
   begin
      VC_Set_Table (E).Include (Id);
   end Add_Id_To_Entity;

   ----------------------------
   -- Decide_Cntexmp_Verdict --
   ----------------------------

   function Decide_Cntexmp_Verdict
     (Small_Step : CE_RAC.Result;
      Giant_Step : CE_RAC.Result;
      VC         : VC_Id;
      Info       : VC_Info)
      return Cntexmp_Verdict
   is
   begin
      case Small_Step.Res_Kind is
         when Res_Failure =>
            if VC_Id (Small_Step.Res_VC_Id) = VC
              and then VC_Kinds_Match (Info.Kind, Small_Step.Res_VC_Kind)
            then
               return (Verdict_Category => Non_Conformity);
            else
               return
                 (Verdict_Category => Bad_Counterexample,
                  Verdict_Reason   => To_Unbounded_String
                    ("normal RAC: failure at a different check "
                     & To_String (Small_Step.Res_VC_Kind, Small_Step.Res_Node)
                     & " instead of " & To_String (Info.Kind, Info.Node)));
            end if;

         when Res_Stuck   =>
            return
              (Verdict_Category => Bad_Counterexample,
               Verdict_Reason   =>
                 "normal RAC stuck: " & Small_Step.Res_Reason);

         when Res_Normal  =>
            case Giant_Step.Res_Kind is
               when Res_Failure =>
                  return (Verdict_Category => Subcontract_Weakness);
               when Res_Normal  =>
                  return
                    (Verdict_Category => Bad_Counterexample,
                     Verdict_Reason   => To_Unbounded_String
                       ("normal/giant-step RAC: no failure"));
               when Res_Stuck   =>
                  return
                    (Verdict_Category => Bad_Counterexample,
                     Verdict_Reason   =>
                        "giant-step RAC stuck: " & Giant_Step.Res_Reason);
               when Res_Incomplete =>
                  return
                    (Verdict_Category => Incomplete,
                     Verdict_Reason   =>
                        "giant-step RAC incomplete: " & Giant_Step.Res_Reason);
               when Res_Not_Executed =>
                  return
                    (Verdict_Category => Incomplete,
                     Verdict_Reason   =>
                        "giant-step RAC not executed: " &
                        Giant_Step.Res_Reason);
            end case;

         when Res_Incomplete =>
            case Giant_Step.Res_Kind is
               when Res_Failure =>
                  return
                    (Verdict_Category =>
                        Non_Conformity_Or_Subcontract_Weakness);
               when Res_Normal  =>
                  return
                    (Verdict_Category => Incomplete,
                     Verdict_Reason   =>
                        "normal RAC incomplete: " & Small_Step.Res_Reason);
               when Res_Stuck   =>
                  return
                    (Verdict_Category => Bad_Counterexample,
                     Verdict_Reason   =>
                        "giant-step RAC stuck: " & Giant_Step.Res_Reason);
               when Res_Incomplete =>
                  return
                    (Verdict_Category => Incomplete,
                     Verdict_Reason   =>
                        "giant-step RAC incomplete: " & Giant_Step.Res_Reason);
               when Res_Not_Executed =>
                  return
                    (Verdict_Category => Incomplete,
                     Verdict_Reason   =>
                        "giant-step RAC not executed: "
                        & Giant_Step.Res_Reason);
            end case;

         when Res_Not_Executed =>
            return
              (Verdict_Category => Incomplete,
               Verdict_Reason   =>
                  "normal RAC not executed: " & Small_Step.Res_Reason);
      end case;
   end Decide_Cntexmp_Verdict;

   -----------------------
   -- Emit_Proof_Result --
   -----------------------

   procedure Emit_Proof_Result
     (Node          : Node_Id;
      Id            : VC_Id;
      Kind          : VC_Kind;
      Proved        : Boolean;
      E             : Entity_Id;
      SD_Id         : Session_Dir_Base_ID;
      How_Proved    : Prover_Category;
      Check_Info    : Check_Info_Type;
      Extra_Msg     : String := "";
      Explanation   : String := "";
      Cntexmp       : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      Verdict       : Cntexmp_Verdict := (others => <>);
      Check_Tree    : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File       : String := "";
      VC_Loc        : Node_Id := Empty;
      Stats         : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd    : String := "";
      Fuzzing_Used  : Boolean := False;
      Print_Fuzzing : Boolean := False)
   is
      function Stat_Message return String;
      --  Prepare a message for statistics of proof results

      function Nice_Float (F : Float) return String;

      ----------------
      -- Nice_Float --
      ----------------

      function Nice_Float (F : Float) return String is
         S : String (1 .. 10);
      begin
         Ada.Float_Text_IO.Put (S, F, 1, 0);
         return Ada.Strings.Fixed.Trim (S, Ada.Strings.Left);
      end Nice_Float;

      ------------------
      -- Stat_Message --
      ------------------

      function Stat_Message return String is
         Buf : Unbounded_String := Null_Unbounded_String;
         use Prover_Stat_Maps;
      begin
         --  Check if VC is not proved or statistics are enabled

         if not Proved or else
           Gnat2Why_Args.Report_Mode not in GPR_Statistics | GPR_Provers
         then
            return "";
         end if;

         --  In case of the check being proved not by Why3, simply identify
         --  this, no need for statistics.

         if How_Proved /= PC_Prover then
            return " (" & To_String (How_Proved) & ")";
         end if;

         --  In the case of missing statistics, don't show them

         if Stats.Is_Empty then
            return "";
         end if;

         --  We are now in the general case (several provers). We first count
         --  the total number of VCs.

         Append (Buf, " (");
         for C in Stats.Iterate loop
            declare
               Elt : Prover_Stat renames Stats (C);
            begin
               Append (Buf, Key (C));
               Append (Buf, ':');
               Append (Buf, Integer'Image (Elt.Count));
               Append (Buf, " VC");
               if Gnat2Why_Args.Report_Mode = GPR_Statistics then
                  Append (Buf, " in max ");
                  Append (Buf, Nice_Float (Elt.Max_Time));
                  Append (Buf, " seconds and");
                  Append (Buf, Positive'Image (Elt.Max_Steps));
                  Append (Buf, " step");
                  if Elt.Max_Steps /= 1 then
                     Append (Buf, 's');
                  end if;
               end if;
               if Has_Element (Next (C)) then
                  Append (Buf, "; ");
               end if;
            end;
         end loop;
         Append (Buf, ')');

         return To_String (Buf);
      end Stat_Message;

   --  Start of processing for Emit_Proof_Result

   begin
      if Kind in VC_Warning_Kind then
         --  VCs that correspond to warnings are only relevant when the prover
         --  could prove them. Discard unproved ones.
         if not Proved then
            return;
         end if;

      elsif Proved then
         Mark_VC_As_Proved_For_Entity (Id, Kind, E);
      end if;

      declare
         Msg : constant String :=
           (if Proved
            then Proved_Message (Node, Kind) & Stat_Message
            else Not_Proved_Message (Node, Kind)
                 & (if CWE then CWE_Message (Kind) else ""))
           & Extra_Msg
           & (if VC_File /= "" then ", vc file: " & VC_File else "");
      begin
         Error_Msg_Proof
           (Node,
            Msg,
            Proved,
            Kind,
            Place_First   => Locate_On_First_Token (Kind),
            Cntexmp       => Cntexmp,
            Verdict       => Verdict,
            Check_Tree    => Check_Tree,
            VC_File       => VC_File,
            VC_Loc        => VC_Loc,
            Editor_Cmd    => Editor_Cmd,
            Explanation   => Explanation,
            Stats         => Stats,
            How_Proved    => How_Proved,
            SD_Id         => SD_Id,
            E             => E,
            Check_Info    => Check_Info,
            Fuzzing_Used  => Fuzzing_Used,
            Print_Fuzzing => Print_Fuzzing);
      end;
   end Emit_Proof_Result;

   ------------------------------
   -- Emit_Static_Proof_Result --
   ------------------------------

   procedure Emit_Static_Proof_Result
     (Node        : Node_Id;
      Kind        : VC_Kind;
      Proved      : Boolean;
      E           : Entity_Id;
      Explanation : String := "")
   is
      Check_Info : constant Check_Info_Type := New_Check_Info;
      Id         : constant VC_Id :=
        Register_VC (Node, Kind, E, Check_Info, Present_In_Why3 => False);
   begin
      Emit_Proof_Result
        (Node,
         Id,
         Kind,
         Proved,
         E,
         No_Session_Dir,
         PC_Trivial,
         Explanation => Explanation,
         Check_Info  => Check_Info);
   end Emit_Static_Proof_Result;

   -------------
   -- Find_VC --
   -------------

   function Find_VC (N : Node_Id; Kind : VC_Kind) return VC_Id is
   begin
      for C in VC_Table.Iterate loop
         if VC_Table (C).Node = N
           and then VC_Table (C).Kind = Kind
         then
            return VC_Id (Id_Tables.To_Index (C));
         end if;
      end loop;

      --  If the exact VC kind was not found, in the case of range-related
      --  checks, look for another range-related VC kind on the same node.

      for C in VC_Table.Iterate loop
         if VC_Table (C).Node = N
           and then VC_Kinds_Match (VC_Table (C).Kind, Kind)
         then
            return VC_Id (Id_Tables.To_Index (C));
         end if;
      end loop;

      if CE_RAC.Do_RAC_Info then
         Ada.Text_IO.Put_Line ("Cannot find " & To_String (Kind, N));
         for C in VC_Table.Iterate loop
            pragma Annotate
              (CodePeer, False_Positive,
               "loop does not complete normally",
               "for loop always terminates");
            Ada.Text_IO.Put_Line
              (" - " & To_String (VC_Table (C).Kind, VC_Table (C).Node));
         end loop;
      end if;

      raise Program_Error with
        ("No VC for node " & Node_Id'Image (N));
   end Find_VC;

   ------------------------
   -- Num_Registered_VCs --
   ------------------------

   function Num_Registered_VCs return Ada.Containers.Count_Type is
     (VC_Table.Length);

   --------------------------------
   -- Num_Registered_VCs_In_Why3 --
   --------------------------------

   function Num_Registered_VCs_In_Why3 return Natural is
      (Registered_VCs_In_Why3);

   -------------------------------------------
   -- Mark_Subprograms_With_No_VC_As_Proved --
   -------------------------------------------

   procedure Mark_Subprograms_With_No_VC_As_Proved
   is
      use Ent_Id_Set_Maps;
   begin
      for C in VC_Set_Table.Iterate loop
         if VC_Set_Table (C).Is_Empty then
            Register_Proof_Claims (Key (C));
         end if;
      end loop;
   end Mark_Subprograms_With_No_VC_As_Proved;

   ----------------------------------
   -- Mark_VC_As_Proved_For_Entity --
   ----------------------------------

   procedure Mark_VC_As_Proved_For_Entity
     (Id   : VC_Id;
      Kind : VC_Kind;
      E    : Entity_Id)
   is
      C : Ent_Id_Set_Maps.Cursor;

   begin
      --  ??? little trick; loop invariant assertions cannot be simply removed,
      --  because there are two of them with the same ID. We fix this by only
      --  counting the "preservation" one, and ignore the "init" one.

      if Kind = VC_Loop_Invariant_Init then
         return;
      end if;

      C := VC_Set_Table.Find (E);
      pragma Assert (Ent_Id_Set_Maps.Has_Element (C));

      VC_Set_Table (C).Delete (Id);

      if VC_Set_Table (C).Is_Empty then
         Register_Proof_Claims (E);
      end if;
   end Mark_VC_As_Proved_For_Entity;

   ------------------------
   -- Not_Proved_Message --
   ------------------------

   function Not_Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String is
   begin
      --  Any change in the messages issued for a check should be reflected in
      --    - GPS plug-in spark2014.py
      --    - the section of SPARK User's Guide on GNATprove

      case Kind is
         --  VC_RTE_Kind - run-time checks

         when VC_Division_Check            =>
            return "divide by zero might fail";
         when VC_Index_Check               =>
            return "array index check might fail";
         when VC_Overflow_Check            =>
            return "overflow check might fail";
         when VC_FP_Overflow_Check            =>
            return "float overflow check might fail";
         when VC_Range_Check               =>
            return "range check might fail";
         when VC_Predicate_Check           =>
            return "predicate check might fail";
         when VC_Predicate_Check_On_Default_Value =>
            return "predicate check might fail on default value";
         when VC_Null_Pointer_Dereference =>
            return "pointer dereference check might fail";
         when VC_Null_Exclusion =>
            return "null exclusion check might fail";
         when VC_Dynamic_Accessibility_Check =>
            return "dynamic accessibility check might fail";
         when VC_Resource_Leak =>
            return "resource or memory leak might occur";
         when VC_Resource_Leak_At_End_Of_Scope =>
            return "resource or memory leak might occur at end of scope";
         when VC_Invariant_Check           =>
            return "invariant check might fail";
         when VC_Invariant_Check_On_Default_Value =>
            return "invariant check might fail on default value";
         when VC_Length_Check              =>
            return "length check might fail";
         when VC_Discriminant_Check        =>
            return "discriminant check might fail";
         when VC_Tag_Check                 =>
            return "tag check might fail";
         when VC_Ceiling_Interrupt         =>
            return "ceiling priority might not be in Interrupt_Priority";
         when VC_Interrupt_Reserved        =>
            return "this interrupt might be reserved";
         when VC_Ceiling_Priority_Protocol =>
            return "ceiling priority protocol might not be respected";
         when VC_Task_Termination          =>
            return "the task might terminate, which is not allowed in SPARK";

         --  VC_Assert_Kind - assertions

         when VC_Initial_Condition         =>
            return "initial condition might fail";
         when VC_Default_Initial_Condition =>
            return "default initial condition might fail";
         when VC_Precondition              =>
            if Nkind (Node) in N_Procedure_Call_Statement
                             | N_Entry_Call_Statement
              and then Is_Error_Signaling_Statement (Node)
            then
               return "call to nonreturning subprogram might be executed";
            else
               return "precondition might fail";
            end if;
         when VC_Precondition_Main         =>
            return "precondition of main program might fail";
         when VC_Postcondition             =>
            return "postcondition might fail";
         when VC_Refined_Post              =>
            return "refined postcondition might fail";
         when VC_Contract_Case             =>
            return "contract case might fail";
         when VC_Disjoint_Contract_Cases   =>
            return "contract cases might not be disjoint";
         when VC_Complete_Contract_Cases   =>
            return "contract cases might not be complete";
         when VC_Loop_Invariant            =>
            return "loop invariant might fail";
         when VC_Loop_Invariant_Init       =>
            return "loop invariant might fail in first iteration";
         when VC_Loop_Invariant_Preserv    =>
            return "loop invariant might not be preserved by an arbitrary " &
              "iteration";
         when VC_Loop_Variant              =>
            return "loop variant might fail";
         when VC_Assert                    =>
            return "assertion might fail";
         when VC_Assert_Premise            =>
            return "assertion premise might fail";
         when VC_Assert_Step               =>
            return "assertion step might fail";
         when VC_Raise                     =>
            --  Give explanations for exceptions which frontend statically
            --  determined to always happen, should the given node be executed.

            if Nkind (Node) in N_Raise_xxx_Error then
               --  ??? The following doesn't work for proving messages manually
               --  in GS, which relies on being able to get back to the VC kind
               --  from the message. A better solution would be to include the
               --  VC kind in the JSON file. Same for Proved_Message.

               case RT_Exception_Code'Val (UI_To_Int (Reason (Node))) is
                  when CE_Range_Check_Failed =>
                     return Not_Proved_Message (Node, VC_Range_Check);
                  when CE_Index_Check_Failed =>
                     return Not_Proved_Message (Node, VC_Index_Check);
                  when CE_Divide_By_Zero =>
                     return Not_Proved_Message (Node, VC_Division_Check);
                  when CE_Access_Check_Failed =>
                     return Not_Proved_Message (Node, VC_Null_Exclusion);
                  when SE_Infinite_Recursion =>

                     --  ??? This message should be reflected in the "Messages
                     --  reported by Proof" SPARK UG table, which is generated
                     --  automatically. Also, it should appear in the
                     --  GNATstudio plugin's vc_fail_msg_dict. Same for
                     --  Proved_Message.

                     return "infinite recursion might occur";

                  --  In debug builds developers will get a crash with a
                  --  missing case, which we will fix whenever it occurs;
                  --  in production builds users will get a generic message.

                  when others =>
                     pragma Assert (False);
               end case;
            end if;
            return "exception might be raised";
         when VC_Inline_Check              =>
            return "Inline_For_Proof or Logical_Equal annotation might be"
              & " incorrect";
         when VC_Subprogram_Variant        =>
            return "subprogram variant might fail";
         when VC_UC_Source               =>
            return "type is unsuitable for unchecked conversion";

         when VC_UC_Target               =>
            declare
               Common : constant String :=
                 " is unsuitable ";
            begin
               if Nkind (Node) in N_Attribute_Reference | N_Object_Declaration
               then
                  return "object" & Common &
                    "for aliasing via address clause";
               else
                  return "type" & Common
                    & "as a target for unchecked conversion";
               end if;
            end;

         when VC_UC_Same_Size              =>
            declare
               Prefix : constant String :=
                 (if Nkind (Node) = N_Attribute_Reference then
                       "types of aliased objects"
                  else "types used for unchecked conversion");
            begin
               return Prefix & " do not have the same size";
            end;

         when VC_UC_Alignment =>
            return "alignment of overlayed object might not be an integral " &
              "multiple of alignment of overlaying object";
         when VC_Initialization_Check      =>
            return "initialization check might fail";
         when VC_Unchecked_Union_Restriction =>
            return "operation on unchecked union type will raise"
              & " Program_Error";

         when VC_UC_Volatile =>
            return "object with non-trivial address clause or prefix of the " &
              "'Address reference does not have asynchronous writers";

         --  VC_LSP_Kind - Liskov Substitution Principle

         when VC_Weaker_Pre                =>
            return "precondition might be stronger than "
              & "class-wide precondition";
         when VC_Trivial_Weaker_Pre        =>
            return "precondition is stronger than the default "
              & "class-wide precondition of True";
         when VC_Stronger_Post             =>
            return "postcondition might be weaker than "
              & "class-wide postcondition";
         when VC_Weaker_Classwide_Pre      =>
            return
              "class-wide precondition might be stronger than overridden one";
         when VC_Stronger_Classwide_Post   =>
            return
              "class-wide postcondition might be weaker than overridden one";

         when VC_Weaker_Pre_Access         =>
            return "precondition of target might not be strong enough to"
              & " imply precondition of source";
         when VC_Stronger_Post_Access      =>
            return "postcondition of source might not be strong enough to"
              & " imply postcondition of target";

         --  VC_Warning_Kind - warnings

         --  Warnings should only be issued when the VC is proved

         when VC_Warning_Kind              =>
            raise Program_Error;
      end case;
   end Not_Proved_Message;

   ------------------------
   -- Parse_Why3_Results --
   ------------------------

   procedure Parse_Why3_Results (Fn : String; Timing : in out Time_Token) is

      --  See the file gnat_report.mli for a description of the format that we
      --  parse here.

      use GNATCOLL.JSON;

      Subp : Entity_Id;

      type Bound_Info_Type is (No_Bound, Low_Bound, High_Bound);

      type Inline_Info (Inline : Boolean := False) is record
         case Inline is
            when False =>
               null;
            when True =>
               Inline_Node : Node_Id;
         end case;
      end record;

      type Extra_Info is record
         Node       : Node_Id;
         Inline     : Inline_Info;
         Bound_Info : Bound_Info_Type;
      end record;

      type Why3_Prove_Result is record
         Id             : VC_Id;
         Kind           : VC_Kind;
         Result         : Boolean;
         EI             : Extra_Info;
         VC_File        : Unbounded_String;
         Editor_Cmd     : Unbounded_String;
         Stats          : Prover_Stat_Maps.Map;
         Cntexmp        : JSON_Value;
         Giant_Step_Res : CE_RAC.Result;
         Check_Tree     : JSON_Value;
      end record;

      function Compute_Cannot_Prove_Message
        (Rec             : Why3_Prove_Result;
         VC              : VC_Info;
         Show_Bound_Info : Boolean := True)
         return String
        with Pre => not Rec.Result;
      --  Function to compute the "cannot prove ..." part of a message. Returns
      --  empty string if no such message can be generated. When the fuzzer is
      --  used to find counterexample values for an overflow check and finds
      --  one that leads to an overflow, we don't check for which bound. The
      --  bound on which the overflow occured isn't displayed in order to avoid
      --  confusion if it was an underflow for an overflow VC. Show_Bound_Info
      --  indicates if the fuzzer was used, in which case don't specify the
      --  bound.

      function Parse_Why3_Prove_Result (V : JSON_Value)
                                        return Why3_Prove_Result;
      --  Parse the JSON produced for Why3 for a single Why3 result record.

      function Parse_Giant_Step_RAC_Result
        (V : JSON_Value) return CE_RAC.Result;
      --  Parse the JSON produced by Why3 for the results of the giant-step RAC

      procedure Handle_Result (V : JSON_Value; SD_Id : Session_Dir_Base_ID);
      --  Parse a single result entry. The entry comes from the session dir
      --  identified by [SD_Id].

      procedure Handle_Error (Msg : String; Internal : Boolean) with No_Return;
      procedure Handle_Timings (V : JSON_Value);

      ----------------------------------
      -- Compute_Cannot_Prove_Message --
      ----------------------------------

      function Compute_Cannot_Prove_Message
        (Rec             : Why3_Prove_Result;
         VC              : VC_Info;
         Show_Bound_Info : Boolean := True)
         return String
      is
         Extra_Text : constant String :=
           (case Rec.EI.Bound_Info is
               when Low_Bound =>
                 (if Show_Bound_Info
                  then "lower bound for "
                  else "bounds for ")
                   & String_Of_Node (Original_Node (VC.Node)),
               when High_Bound =>
                 (if Show_Bound_Info
                  then "upper bound for "
                  else "bounds for ")
                   & String_Of_Node (Original_Node (VC.Node)),
               when No_Bound =>
                 (if Present (Rec.EI.Node)
                  and then VC.Node /= Rec.EI.Node
                  then String_Of_Node (Original_Node (Rec.EI.Node))
                  else "")
           );
      begin
         if Extra_Text /= "" then
            return ", cannot prove " & Extra_Text;
         else
            return "";
         end if;
      end Compute_Cannot_Prove_Message;

      ------------------
      -- Handle_Error --
      ------------------

      procedure Handle_Error (Msg : String; Internal : Boolean) is
      begin
         --  For errors in gnatwhy3 the source code location is meaningless
         Current_Error_Node := Empty;

         if Internal then
            --  The bugbox generated by the Compiler_Abort routine will either
            --  contain a sloc of the last exception (which is useless, because
            --  the last exception happend when the gnatwhy3 process died, and
            --  was expected), or a generic "GCC error". The latter seems less
            --  confusing for the user.

            Compiler_Abort (Msg, From_GCC => True);
         else
            Ada.Text_IO.Put ("gnatprove: ");
            Ada.Text_IO.Put_Line (Msg);
            Exit_Program (E_Fatal);
         end if;
      end Handle_Error;

      -------------------
      -- Handle_Result --
      -------------------

      procedure Handle_Result (V : JSON_Value; SD_Id : Session_Dir_Base_ID) is

         procedure Check_Counterexample
           (Rec            :     Why3_Prove_Result;
            VC             :     VC_Info;
            Cntexmp        :     Cntexample_File_Maps.Map;
            Fuel           :     Fuel_Access;
            Small_Step_Res : out CE_RAC.Result;
            Verdict        : out Cntexmp_Verdict;
            Use_Fuzzing    :     Boolean := False);
         --  Call the small step RAC to check the counterexample and create
         --  the appropriate verdict.

         procedure Free is new
           Ada.Unchecked_Deallocation (Fuel_Type, Fuel_Access);
         --  Release memory used by the fuel

         function To_Initialize_Present (E : Entity_Id) return Boolean;
         --  Determine if the subprogram has global variables that can be
         --  initialized or if the function has IN parameters.

         function Small_Step_Rac
           (E           : Entity_Id;
            Cntexmp     : Cntexample_File_Maps.Map;
            VC          : Node_Id;
            Fuel        : Fuel_Access;
            Use_Fuzzing : Boolean := False)
            return CE_RAC.Result;
         --  Run CE_RAC.Execute and print some debugging info if requested

         --------------------------
         -- Check_Counterexample --
         --------------------------

         procedure Check_Counterexample
           (Rec            :     Why3_Prove_Result;
            VC             :     VC_Info;
            Cntexmp        :     Cntexample_File_Maps.Map;
            Fuel           :     Fuel_Access;
            Small_Step_Res : out CE_RAC.Result;
            Verdict        : out Cntexmp_Verdict;
            Use_Fuzzing    :     Boolean := False)
         is
         begin
            Small_Step_Res :=
              Small_Step_Rac
                (Subp, Cntexmp, VC.Node, Fuel, Use_Fuzzing);

            if Small_Step_Res.Res_Kind = CE_RAC.Res_Failure then
               begin
                  Small_Step_Res.Res_VC_Id :=
                    Natural
                      (Find_VC
                         (Small_Step_Res.Res_Node,
                          Small_Step_Res.Res_VC_Kind));
               exception
                  when E : Program_Error =>
                     --  Find_VC raises a Program_Error when unsuccessful
                     --  but we want to handle it like an unexpected RAC
                     --  error
                     raise RAC_Unexpected_Error with
                     Ada.Exceptions.Exception_Message (E);
               end;
            end if;

            Verdict := Decide_Cntexmp_Verdict
              (Small_Step_Res, Rec.Giant_Step_Res, Rec.Id, VC);
         exception
            when E : others =>
               if Debug_Flag_K
                 and then Exception_Identity (E)
                 /= RAC_Unexpected_Error'Identity
               --  We accept RAC_Unexpected_Error for now
               --  ??? In Find_VC it can just result in RES_INCOMPLETE,
               --  during CE value import this could be RAC_Unsupported
               --  for now, and should be fixed
               then
                  raise;
               else
                  Small_Step_Res :=
                    (Res_Kind   => Res_Incomplete,
                     Res_Reason => To_Unbounded_String
                       (Exception_Name (E) & ": " & Exception_Message (E)));
                  Verdict := Decide_Cntexmp_Verdict
                    (Small_Step_Res, Rec.Giant_Step_Res, Rec.Id, VC);
               end if;
         end Check_Counterexample;

         ---------------------------
         -- To_Initialize_Present --
         ---------------------------

         function To_Initialize_Present (E : Entity_Id) return Boolean
         is
            Reads, Writes : Flow_Id_Sets.Set;
            Scope         : constant Flow_Scope := Get_Flow_Scope (E);
         begin
            Get_Proof_Globals
              (E, Reads, Writes, False, Scope);
            --  Check that there are globals, i.e. that running the fuzzer
            --  would have an effect. This is done to prevent the fuzzing
            --  session to never stop when the verdict cannot be affected by
            --  the fuzzer.

            for Id of Reads loop
               if Id.Kind = Direct_Mapping then
                  return True;
               end if;
            end loop;

            declare
               Param : Entity_Id := First_Formal (E);
            begin
               while Present (Param) loop
                  if Ekind (Param) /= E_Out_Parameter then
                     return True;
                  end if;
                  Next_Formal (Param);
               end loop;
            end;

            return False;
         end To_Initialize_Present;

         --------------------
         -- Small_Step_Rac --
         --------------------

         function Small_Step_Rac
           (E           : Entity_Id;
            Cntexmp     : Cntexample_File_Maps.Map;
            VC          : Node_Id;
            Fuel        : Fuel_Access;
            Use_Fuzzing : Boolean := False)
            return CE_RAC.Result
         is
         begin
            if CE_RAC.Do_RAC_Info then
               Write_Str ("VC at ");
               Write_Location (Sloc (VC));
               Write_Eol;
            end if;
            return CE_RAC.RAC_Execute
              (E,
               Cntexmp,
               Do_Sideeffects => False,
               Fuel           => Fuel,
               Stack_Height   => 100,
               Use_Fuzzing    => Use_Fuzzing);
            --  During execution CE_RAC counts the stacked calls in the
            --  interpreted program and terminates as incomplete when the
            --  stack height is exceeded. We cannot really know how many
            --  calls are in the interpreter between each call in the
            --  interpreted program to anticipate a GNAT stackoverflow, but the
            --  above value seems to work.
         end Small_Step_Rac;

         --  Local variables

         Rec            : constant Why3_Prove_Result :=
           Parse_Why3_Prove_Result (V);
         VC             : VC_Info renames VC_Table (Rec.Id);
         Can_Relocate : constant Boolean :=
           Rec.Kind not in VC_Precondition
                         | VC_LSP_Kind
                         | VC_Predicate_Check
                         | VC_Predicate_Check_On_Default_Value;
         Node       : constant Node_Id :=
           (if Present (Rec.EI.Node)
            and then not Rec.EI.Inline.Inline
            and then Can_Relocate
            then
               Rec.EI.Node
            elsif Rec.EI.Inline.Inline
            and then Present (Rec.EI.Inline.Inline_Node)
            and then Can_Relocate
            then
               Rec.EI.Inline.Inline_Node
            else VC.Node);
         --  VC_Sloc contains the location of the check (required in messages
         --  for manual provers). The extra info data ("EI") may contain a more
         --  precise location which is used to place the error message.
         --  If the inline flag is set, we don't use the EI node, but we
         --  may use the EI.Inline node, which contains the context before
         --  inlining.
         --  We do not any of those extra nodes if the node may switch the
         --  context, (negation of the Can_Relocate flag) this can happen for
         --  the pre (the node will be in the callee context instead of the
         --  caller context) and LSP VCs as well as predicate checks.
         VC_Sloc            : constant Node_Id := VC.Node;
         Small_Step_Res     : CE_RAC.Result;
         Verdict            : Cntexmp_Verdict;
         Small_Step_Res_Tmp : CE_RAC.Result;
         Verdict_Tmp        : Cntexmp_Verdict;
         Cntexmp            : constant Cntexample_File_Maps.Map :=
           From_JSON (Rec.Cntexmp);
         Check_Info         : Check_Info_Type := VC.Check_Info;
         Fuel               : Fuel_Access := new Fuel_Type'(250_000);
         Cntexmp_Present    : constant Boolean := not Cntexmp.Is_Empty;
         Fuzzing_Used       : Boolean := False;
         Print_Fuzzing      : Boolean := False;

      --  Start of processing for Handle_Result

      begin
         if Gnat2Why_Args.Check_Counterexamples
           and then not Rec.Result
         then
            if Cntexmp_Present then
               --  Check the counterexample like normal

               Check_Counterexample
                 (Rec, VC, Cntexmp, Fuel, Small_Step_Res, Verdict);
            else
               Small_Step_Res :=
                 (Res_Kind   => Res_Not_Executed,
                  Res_Reason => To_Unbounded_String ("No counterexample"));
               Verdict :=
                 (Verdict_Category => Not_Checked,
                  Verdict_Reason   => To_Unbounded_String
                    ("No counterexample"));
            end if;

            --  Only call the fuzzer when there are global variables or
            --  function parameters on which it can have an impact. CE checking
            --  should not be done when the VC is a warning, so the fuzzer
            --  should be not used either. If the giant step RAC resulted in
            --  Res_Failure, the CE exhibits a behaviour of the program that is
            --  not the expected one and is worth keeping, so the fuzzer
            --  shouldn't be used.

            if VC.Kind not in VC_Warning_Kind
              and then Rec.Giant_Step_Res.Res_Kind not in Res_Failure
              and then Ekind (Subp) in E_Function | E_Procedure
              and then To_Initialize_Present (Subp)
            then
               --  Begin fuzzing

               --  It is worth using the fuzzer to look for a better
               --  counterexample than that provided by the prover if:
               --
               --    * The small step RAC detected a problem (Res_Failure) but
               --      not the expected one (Bad_Counterexample verdict);
               --
               --    * The small step RAC was not used yet (no CE to check);
               --
               --    * No execution defect was observed (Res_Normal);
               --
               --    * The small step RAC got stuck (RAC_Stuck), in which case
               --      it is possible that another value might lead to a
               --      different execution path in which the RAC won't get
               --      stuck.

               --  Use a temporary copy of the small step RAC result and the
               --  verdict and operate on it for fuzzing.
               --  Update the official result and verdict only if fuzzing
               --  produces a good CE.
               Small_Step_Res_Tmp := Small_Step_Res;
               Verdict_Tmp := Verdict;

               while Fuel.all > 0
                 and then
                   ((Small_Step_Res_Tmp.Res_Kind in Res_Failure
                     and then
                     Verdict_Tmp.Verdict_Category in Bad_Counterexample)
                    or else
                    Small_Step_Res_Tmp.Res_Kind in
                      Res_Not_Executed | Res_Normal | Res_Stuck)
               loop
                  Check_Fuel_Decrease (Fuel, 100);
                  Fuzzing_Used := True;

                  Check_Counterexample
                    (Rec            => Rec,
                     VC             => VC,
                     Cntexmp        => Cntexmp,
                     Fuel           => Fuel,
                     Small_Step_Res => Small_Step_Res_Tmp,
                     Verdict        => Verdict_Tmp,
                     Use_Fuzzing    => True);
               end loop;

               --  Check if the fuzzing produced a good CE, i.e. not bad nor
               --  incomplete.
               if Verdict_Tmp.Verdict_Category not in
                 Bad_Counterexample | Incomplete
               then
                  Small_Step_Res := Small_Step_Res_Tmp;
                  Verdict := Verdict_Tmp;
               end if;

            end if;

         else
            Verdict :=
              (Verdict_Category => Not_Checked,
               Verdict_Reason   => To_Unbounded_String
                 ("Counterexample checking not requested"));
         end if;

         --  Do not print verdict and RAC results if the VC is proved
         if not Rec.Result
           and then CE_RAC.Do_RAC_Info
         then
            Write_Str
              ("----------"
               & LF & "VERDICT: "
               & Verdict.Verdict_Category'Image
               & ", Reason: "      & Reason (Verdict)
               & " | Small-step: " & Small_Step_Res.Res_Kind'Image
               & ", Reason: "      & Reason (Small_Step_Res)
               & " | Giant-step: " & Rec.Giant_Step_Res.Res_Kind'Image
               & ", Reason: "      & Reason (Rec.Giant_Step_Res)
               & LF & "----------"
               & LF);
            Write_Location (Sloc (VC.Node));
            Write_Eol;
         end if;

         --  Actually print the values used by the fuzzer if the execution
         --  ended in failure. Fuzzing can be interrupted before it finds
         --  satisfying values by the fuel running out. In this case we still
         --  don't want the values to be displayed.

         Print_Fuzzing := Fuzzing_Used
           and then Small_Step_Res.Res_Kind = Res_Failure
           and then Small_Step_Res.Res_Node = VC.Node;

         --  If the VC comes from an inlined predicate or expression function
         --  body, then add a continuation referencing the unproved node in
         --  the inlined expression.

         if Rec.EI.Inline.Inline
           and then Present (Rec.EI.Node)
         then
            declare
               function Is_Subprogram_Body (X : Node_Id) return Boolean is
                 (Nkind (X) = N_Subprogram_Body);
               function Enclosing_Subprogram is new First_Parent_With_Property
                 (Is_Subprogram_Body);

               Subp_Body    : constant Node_Id :=
                 Enclosing_Subprogram (Rec.EI.Node);
               In_Predicate : constant Boolean :=
                 Present (Subp_Body)
                 and then Is_Predicate_Function
                   (Unique_Defining_Entity (Subp_Body));
               --  To know whether we are inlining an expression function or
               --  a predicate, look for the encolsing subprogram body, and
               --  check if it is a predicate function.

            begin
               Check_Info.Continuation.Append
                 (Continuation_Type'
                    (Rec.EI.Node,
                     To_Unbounded_String
                       ("in inlined " &
                        (if In_Predicate then "predicate"
                           else "expression function body"))));
            end;
         end if;

         declare
            --  If the fuzzer found a counterexample for a VC associated to an
            --  overflow check, the message saying if the overflow was on the
            --  lower or upper bound might be wrong since it depends on the
            --  giant-step RAC's result. For now when the fuzzer was used,
            --  don't distinguish between upper or lower bound overflow.

            CP_Msg : constant String :=
              (if not Rec.Result
               then Compute_Cannot_Prove_Message
                 (Rec             => Rec,
                  VC              => VC,
                  Show_Bound_Info => not Print_Fuzzing)
               else "");
         begin
            Emit_Proof_Result
              (Node          => Node,
               Id            => Rec.Id,
               Kind          => Rec.Kind,
               Proved        => Rec.Result,
               E             => Subp,
               SD_Id         => SD_Id,
               How_Proved    => PC_Prover,
               Cntexmp       => Rec.Cntexmp,
               Verdict       => Verdict,
               Check_Tree    => Rec.Check_Tree,
               VC_File       => To_String (Rec.VC_File),
               VC_Loc        => VC_Sloc,
               Editor_Cmd    => To_String (Rec.Editor_Cmd),
               Stats         => Rec.Stats,
               Extra_Msg     => CP_Msg,
               Check_Info    => Check_Info,
               Fuzzing_Used  => Fuzzing_Used,
               Print_Fuzzing => Print_Fuzzing);
         end;

         Free (Fuel);
      end Handle_Result;

      --------------------
      -- Handle_Timings --
      --------------------

      procedure Handle_Timings (V : JSON_Value) is
         procedure Timing_Entry (Name : UTF8_String; Value : JSON_Value);

         ------------------
         -- Timing_Entry --
         ------------------

         procedure Timing_Entry (Name : UTF8_String; Value : JSON_Value) is
            Time : constant Float := Get (Value);
         begin
            Register_Timing (Timing, Name, Duration (Time));
         end Timing_Entry;

      --  Start of processing for Handle_Timings

      begin
         Map_JSON_Object (V, Timing_Entry'Access);
      end Handle_Timings;

      ---------------------------------
      -- Parse_Giant_Step_RAC_Result --
      ---------------------------------

      function Parse_Giant_Step_RAC_Result
        (V : JSON_Value) return CE_RAC.Result is
         Check : JSON_Value;
      begin
         if V = JSON_Null then
            return
              (Res_Kind   => Res_Incomplete,
               Res_Reason => To_Unbounded_String
                 ("no giant-step RAC result"));
         else
            declare
               State : constant String := Get (V, "state");
            begin
               if State = "NORMAL" then
                  return
                    (Res_Kind  => Res_Normal,
                     Res_Value => (Present => False));
               elsif State = "FAILURE" then
                  Check := Get (V, "check");
                  if Check = JSON_Null then
                     return (Res_Kind   => Res_Not_Executed,
                             Res_Reason =>
                               To_Unbounded_String
                                 ("Giant-step RAC failed but the check is " &
                                    "missing from the output"));
                  else
                     return
                       (Res_Kind  => Res_Failure,
                        Res_Node  => Empty,
                        Res_VC_Id =>
                          Natural (Integer'(Get (Check, "id"))),
                        Res_VC_Kind => VC_Kind'Value
                          (Get (Check, "vc_kind")));
                  end if;
               elsif State = "STUCK" then
                  return
                    (Res_Kind   => Res_Stuck,
                     Res_Reason => To_Unbounded_String
                       (String'(Get (V, "reason"))));
               elsif State = "INCOMPLETE" then
                  return
                    (Res_Kind   => Res_Incomplete,
                     Res_Reason => To_Unbounded_String
                       (String'(Get (V, "reason"))));
               else
                  raise Program_Error with
                    ("unexpected result state for giant-step RAC " &
                       State);
               end if;
            end;
         end if;
      end Parse_Giant_Step_RAC_Result;

      -----------------------------
      -- Parse_Why3_Prove_Result --
      -----------------------------

      function Parse_Why3_Prove_Result (V : JSON_Value)
                                        return Why3_Prove_Result is
         E : Extra_Info := (0, Inline_Info'(Inline => False), No_Bound);
      begin
         if Has_Field (V, "extra_info") then
            declare
               I : constant Integer :=
                 Integer'(Get (Get (V, "extra_info"), "node"));
            begin
               if I = Low_Bound_Id then
                  E.Bound_Info := Low_Bound;
               elsif I = High_Bound_Id then
                  E.Bound_Info := High_Bound;
               else
                  E.Node := Node_Id (I);
               end if;
            end;
            declare
               I : constant Integer :=
                 Integer'(Get (Get (V, "extra_info"), "inline"));
            begin
               if I < 0 then
                  E.Inline := Inline_Info'(True, 0);
               elsif I = 0 then
                  E.Inline := Inline_Info'(Inline => False);
               else
                  E.Inline := Inline_Info'(True, Node_Id (I));
               end if;
            end;
         end if;
         return Why3_Prove_Result'
           (Id         => VC_Id (Integer'(Get (Get (V, "id")))),
            Kind       => VC_Kind'Value (Get (Get (V, "reason"))),
            Result     => Get (Get (V, "result")),
            EI         => E,
            VC_File    =>
            (if Has_Field (V, "vc_file") then Get (Get (V, "vc_file"))
             else Null_Unbounded_String),
            Editor_Cmd =>
              (if Has_Field (V, "editor_cmd") then Get (Get (V, "editor_cmd"))
               else Null_Unbounded_String),
            Stats      =>
              (if Has_Field (V, "stats") then From_JSON (Get (V, "stats"))
               else Prover_Stat_Maps.Empty_Map),
            Cntexmp    =>
              (if Has_Field (V, "cntexmp") then Get (V, "cntexmp")
               else Create_Object),
            Giant_Step_Res =>
              (if Has_Field (V, "giant_step_rac_result")
               then Parse_Giant_Step_RAC_Result
                 (Get (V, "giant_step_rac_result"))
               else
                 (Res_Kind   => Res_Not_Executed,
                  Res_Reason => To_Unbounded_String ("No giant-step result"))),
            Check_Tree =>
              (if Has_Field (V, "check_tree") then Get (V, "check_tree")
               else Create_Object));
      end Parse_Why3_Prove_Result;

   --  Start of processing for Parse_Why3_Results

   begin
      Mark_Subprograms_With_No_VC_As_Proved;

      declare
         File    : constant JSON_Value := Read_File_Into_JSON (Fn);
         Results : constant JSON_Array := Get (Get (File, "results"));
         SD_Id   : Session_Dir_Base_ID := 0;
      begin
         if Has_Field (File, "error") then
            declare
               Msg      : constant String := Get (Get (File, "error"));
               Internal : constant Boolean :=
                 Has_Field (File, "internal")
                   and then Get (Get (File, "internal"));
            begin
               Handle_Error (Msg, Internal);
            end;
         end if;
         Subp := Entity_Id (Integer'(Get (File, "entity")));
         if Has_Field (File, "session_dir") then
            SD_Id := Register_Session_Dir (Get (Get (File, "session_dir")));
         end if;
         if Has_Field (File, "timings") then
            Handle_Timings (Get (File, "timings"));
         end if;
         for Index in 1 .. Length (Results) loop
            Handle_Result (Get (Results, Index), SD_Id);
         end loop;
         if Has_Field (File, "warnings") then
            declare
               Warnings : constant JSON_Array := Get (Get (File, "warnings"));
            begin
               for Index in 1 .. Length (Warnings) loop

                  --  ??? Use some other mechanism to print those messages?

                  Ada.Text_IO.Put_Line (Get (Get (Warnings, Index)));
               end loop;
            end;
         end if;
      end;
   exception
      when Error : Invalid_JSON_Stream =>
         declare
            Error_Msg : constant String :=
              Ada.Exceptions.Exception_Message (Error);

            OOM_Prefix : constant String := "Fatal error: out of memory";
            --  If there is an "Out of memory" (or OOM) exception in the OCaml
            --  runtime we get this message, possibly followed by extra info.

         begin
            --  If it is an OOM error, then output the prefix alone

            if Head (Error_Msg, OOM_Prefix'Length) = OOM_Prefix then
               Handle_Error (OOM_Prefix, Internal => False);

            --  Otherwise, output gnatwhy3 error as is

            else
               Handle_Error (Error_Msg, Internal => True);
            end if;
         end;
   end Parse_Why3_Results;

   --------------------
   -- Proved_Message --
   --------------------

   function Proved_Message (Node : Node_Id; Kind : VC_Kind) return String is
      function Inst is new VC_Message (Verb => "proved");
   begin
      return Inst (Node, Kind);
   end Proved_Message;

   -----------------
   -- Register_VC --
   -----------------

   function Register_VC
     (N               : Node_Id;
      Reason          : VC_Kind;
      E               : Entity_Id;
      Check_Info      : Check_Info_Type;
      Present_In_Why3 : Boolean := True)
      return VC_Id
   is
      Registered_Id : VC_Id;
   begin
      VC_Table.Append (VC_Info'(N, Reason, Check_Info));
      Registered_Id := VC_Table.Last_Index;

      --  Do not consider warnings in the set of checks associated to an
      --  entity, to decide whether the entity was fully verified or not.
      if Reason not in VC_Warning_Kind then
         Add_Id_To_Entity (Registered_Id, E);
      end if;

      if Present_In_Why3 then
         Registered_VCs_In_Why3 := Registered_VCs_In_Why3 + 1;
      end if;
      return Registered_Id;
   end Register_VC;

   ------------------------
   -- Register_VC_Entity --
   ------------------------

   procedure Register_VC_Entity (E : Entity_Id) is
      Position : Ent_Id_Set_Maps.Cursor;
      Unused   : Boolean;
   begin
      VC_Set_Table.Insert (Key => E, Position => Position, Inserted => Unused);
   end Register_VC_Entity;

   -----------------
   -- VC_Messsage --
   -----------------

   function VC_Message (Node : Node_Id; Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check            =>
            return "division check " & Verb;
         when VC_Index_Check               => return "index check " & Verb;
         when VC_Overflow_Check            =>
            return "overflow check " & Verb;
         when VC_FP_Overflow_Check         =>
            return "float overflow check " & Verb;
         when VC_Range_Check               => return "range check " & Verb;
         when VC_Predicate_Check           =>
            return "predicate check " & Verb;
         when VC_Predicate_Check_On_Default_Value =>
            return "predicate check " & Verb & " on default value";
         when VC_Null_Pointer_Dereference =>
            return "pointer dereference check " & Verb;
         when VC_Null_Exclusion =>
            return "null exclusion check " & Verb;
         when VC_Dynamic_Accessibility_Check =>
            return "dynamic accessibility check " & Verb;
         when VC_Resource_Leak =>
            return "absence of resource or memory leak " & Verb;
         when VC_Resource_Leak_At_End_Of_Scope =>
            return "absence of resource or memory leak at end of scope "
              & Verb;
         when VC_Invariant_Check           =>
            return "invariant check " & Verb;
         when VC_Invariant_Check_On_Default_Value =>
            return "invariant check " & Verb & " on default value";
         when VC_Length_Check              => return "length check " & Verb;
         when VC_Discriminant_Check        =>
            return "discriminant check " & Verb;
         when VC_Tag_Check                 => return "tag check " & Verb;
         when VC_Ceiling_Interrupt         =>
            return "ceiling priority in Interrupt_Priority " & Verb;
         when VC_Interrupt_Reserved        =>
            return "availability of interrupt " & Verb;
         when VC_Ceiling_Priority_Protocol =>
            return Prefix & "ceiling priority protocol is respected";
         when VC_Task_Termination          =>
            return "nontermination of task " & Verb;

         when VC_Initial_Condition         =>
            return "initial condition " & Verb;
         when VC_Default_Initial_Condition =>
            return "default initial condition " & Verb;
         when VC_Precondition              =>
            if Nkind (Node) in N_Procedure_Call_Statement
                             | N_Entry_Call_Statement
              and then Is_Error_Signaling_Statement (Node)
            then
               return Prefix & "call to nonreturning procedure never executed";
            else
               return "precondition " & Verb;
            end if;
         when VC_Precondition_Main         =>
            return "precondition of main program " & Verb;
         when VC_Postcondition             => return "postcondition " & Verb;
         when VC_Refined_Post              => return "refined post " & Verb;
         when VC_Contract_Case             => return "contract case " & Verb;
         when VC_Disjoint_Contract_Cases   =>
            return "disjoint contract cases " & Verb;
         when VC_Complete_Contract_Cases   =>
            return "complete contract cases " & Verb;
         when VC_Loop_Invariant            =>
            return "loop invariant " & Verb;
         when VC_Loop_Invariant_Init       =>
            return "loop invariant initialization " & Verb;
         when VC_Loop_Invariant_Preserv    =>
            return "loop invariant preservation " & Verb;
         when VC_Loop_Variant              => return "loop variant " & Verb;
         when VC_Assert                    => return "assertion " & Verb;
         when VC_Assert_Premise            =>
            return "assertion premise " & Verb;
         when VC_Assert_Step               => return "assertion step " & Verb;
         when VC_Raise                     =>
            --  Give explanations for exceptions which frontend statically
            --  determined to always happen, but backend proved to be
            --  unreachable.

            if Nkind (Node) in N_Raise_xxx_Error then
               case RT_Exception_Code'Val (UI_To_Int (Reason (Node))) is
                  when CE_Range_Check_Failed =>
                     return VC_Message (Node, VC_Range_Check);
                  when CE_Index_Check_Failed =>
                     return VC_Message (Node, VC_Index_Check);
                  when CE_Divide_By_Zero =>
                     return VC_Message (Node, VC_Division_Check);
                  when SE_Infinite_Recursion =>
                     return "infinite recursion " & Verb & " unreachable";

                  --  In debug builds developers will get a crash with a
                  --  missing case, which we will fix whenever it occurs;
                  --  in production builds users will get a generic message.

                  when others =>
                     pragma Assert (False);
               end case;
            end if;
            return "raise statement or expression " & Verb & " unreachable";
         when VC_Inline_Check              =>
            return "Inline_For_Proof or Logical_Equal annotation " & Verb;
         when VC_Subprogram_Variant        =>
            return "subprogram variant " & Verb;
         when VC_UC_Source                 =>
            return Prefix
              & "type is suitable as source for unchecked conversion";
         when VC_UC_Target                 =>
            declare
               Common : constant String := " is suitable for ";
            begin
               if Nkind (Node) in N_Attribute_Reference | N_Object_Declaration
               then
                  return Prefix & "object" & Common &
                    "aliasing via address clause";
               else
                  return Prefix & "type" & Common & "unchecked conversion";
               end if;
            end;

         when VC_UC_Same_Size              =>
            if Nkind (Node) = N_Attribute_Reference then
               return Prefix & "types of aliased objects have the same size";
            else
               return Prefix
                 & "types in unchecked conversion have the same size";
            end if;

         when VC_UC_Alignment =>
            return Prefix & "alignment of overlaid objects is compatible";

         when VC_UC_Volatile =>
            return Prefix
              & "object with non-trivial address clause and prefix of the"
              & " 'Address attribute have asynchronous writers";

         when VC_Weaker_Pre                =>
            return Prefix & "precondition is weaker than"
              & " class-wide precondition";
         when VC_Trivial_Weaker_Pre        =>
            return Prefix & "precondition is always True";
         when VC_Stronger_Post             =>
            return Prefix & "postcondition is stronger"
              & " than class-wide postcondition";
         when VC_Weaker_Classwide_Pre      =>
            return Prefix
              & "class-wide precondition is weaker than overridden one";
         when VC_Stronger_Classwide_Post   =>
            return Prefix & "class-wide postcondition is stronger"
              & " than overridden one";
         when VC_Weaker_Pre_Access         =>
            return Prefix & "precondition of target is strong enough to imply"
              & " precondition of source";
         when VC_Stronger_Post_Access      =>
            return Prefix & "postcondition of source is strong enough to imply"
              & " postcondition of target";
         when VC_Initialization_Check      =>
            return "initialization check " & Verb;
         when VC_Unchecked_Union_Restriction =>
            return "operation on unchecked union type " & Verb;

         --  VC_Warning_Kind - warnings

         when VC_Inconsistent_Pre          =>
            return Prefix & "precondition is always False";
         when VC_Inconsistent_Post         =>
            return Prefix & "postcondition is always False";
         when VC_Inconsistent_Assume         =>
            return Prefix & "pragma Assume is always False";
         when VC_Unreachable_Branch        =>
            return "unreachable branch" & Suffix;
         when VC_Dead_Code                 =>
            return "unreachable code" & Suffix;
      end case;
   end VC_Message;

end Gnat2Why.Error_Messages;
