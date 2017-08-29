------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2014-2017, AdaCore                   --
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

with Ada.Strings;
with Ada.Strings.Fixed;
with Ada.Containers;
with Ada.Containers.Vectors;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Indefinite_Hashed_Sets;
with Ada.Directories;           use Ada.Directories;
with Ada.Float_Text_IO;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Common_Containers;         use Common_Containers;
with Comperr;                   use Comperr;
with Einfo;                     use Einfo;
with Errout;                    use Errout;
with Flow_Error_Messages;       use Flow_Error_Messages;
with Gnat2Why.Assumptions;      use Gnat2Why.Assumptions;
with Gnat2Why_Args;             use Gnat2Why_Args;
with Lib.Xref;
with Osint;                     use Osint;
with SA_Messages;               use SA_Messages;
with Sem_Aux;                   use Sem_Aux;
with Sem_Util;                  use Sem_Util;
with Sinfo;                     use Sinfo;
with Sinput;                    use Sinput;
with SPARK_Util;                use SPARK_Util;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;

package body Gnat2Why.Error_Messages is

   type VC_Info is record
      Node   : Node_Id;
      Entity : Entity_Id;
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

   package Msg_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (Element_Type        => SA_Messages.Message_And_Location,
      Hash                => SA_Messages.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id);
   --  Enter the VC_Id into the map from entities to Id_Sets

   procedure Mark_VC_As_Proved_For_Entity
     (Id   : VC_Id;
      Kind : VC_Kind;
      E    : Entity_Id);
   --  Remove the VC_Id from the map from entities to Id_Sets

   procedure Mark_Subprograms_With_No_VC_As_Proved;
   --  For all subprograms that do not contain any VC, issue related claims

   function Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  Return the message string for a proved VC

   function Not_Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String;
   --  Return the message string for an unproved VC

   VC_Table : Id_Tables.Vector := Id_Tables.Empty_Vector;
   --  This table maps ids to their VC_Info (entity and Ada node)

   VC_Set_Table : Ent_Id_Set_Maps.Map := Ent_Id_Set_Maps.Empty_Map;
   --  This table maps entities to the set of unproved VCs

   Codepeer_Proved : Msg_Sets.Set;
   --  This set contains the checks that codepeer has proved

   CP_File_Present : Boolean := False;
   --  Set to true when CodePeer results have been found - this allows to skip
   --  costly work in case when codepeer is not there.

   ----------------------
   -- Add_Id_To_Entity --
   ----------------------

   procedure Add_Id_To_Entity (Id : VC_Id; E : Entity_Id) is
   begin
      VC_Set_Table (E).Include (Id);
   end Add_Id_To_Entity;

   -------------------------
   -- CodePeer_Has_Proved --
   -------------------------

   function CodePeer_Has_Proved (Slc : Source_Ptr; Kind : VC_Kind)
                                 return Boolean is

      function Make_CodePeer_Loc (Sloc : Source_Ptr) return Source_Location;
      --  @param Sloc a source location as defined by the GNAT front-end
      --  @return the equivalent a source location in the type defined by the
      --    SA_Messages unit

      type Opt_Msg (OK : Boolean) is record
         case OK is
            when True =>
               Msg : SA_Message;
            when False =>
               null;
         end case;
      end record;

      function Make_Codepeer_Msg (Kind : VC_Kind) return Opt_Msg;
      --  @param Kind a VC Kind as defined by gnat2why
      --  @return the same VC kind as defined by the type in the SA_Messages
      --    unit. We use an option type here to allow not returning such a
      --    kind. This is useful in the cases where there is no equivalent in
      --    SA_Messages or when the mapping is not clear.

      -----------------------
      -- Make_CodePeer_Loc --
      -----------------------

      function Make_CodePeer_Loc (Sloc : Source_Ptr) return Source_Location is
      begin
         if Sloc = No_Location then
            return Null_Location;
         else
            return Make (File_Name (Slc),
                         Line_Number (Get_Physical_Line_Number (Slc)),
                         SA_Messages.Column_Number (Get_Column_Number (Slc)),
                         Iteration_Id'(Kind => None),
                         Make_CodePeer_Loc (Instantiation_Location (Sloc)));
         end if;
      end Make_CodePeer_Loc;

      -----------------------
      -- Make_Codepeer_Msg --
      -----------------------

      function Make_Codepeer_Msg (Kind : VC_Kind) return Opt_Msg is
      begin
         case Kind is
            when VC_Division_Check =>
               return (True,
                       SA_Message'(Divide_By_Zero_Check,
                                   Statically_Known_Success));

            when VC_Index_Check    =>
               return (True,
                       SA_Message'(Array_Index_Check,
                                   Statically_Known_Success));

            when VC_Overflow_Check | VC_FP_Overflow_Check =>
               return (True,
                       SA_Message'(SA_Messages.Overflow_Check,
                                   Statically_Known_Success));

            when VC_Range_Check    =>
               return (True,
                       SA_Message'(SA_Messages.Range_Check,
                                   Statically_Known_Success));

            when VC_Discriminant_Check =>
               return (True,
                       SA_Message'(SA_Messages.Discriminant_Check,
                                   Statically_Known_Success));

            when VC_Tag_Check =>
               return (True,
                       SA_Message'(SA_Messages.Tag_Check,
                                   Statically_Known_Success));

            when VC_Precondition
               | VC_Precondition_Main
               | VC_Postcondition
               | VC_Initial_Condition
               | VC_Default_Initial_Condition
               | VC_Refined_Post
               | VC_Contract_Case
               | VC_Disjoint_Contract_Cases
               | VC_Complete_Contract_Cases
               | VC_Loop_Variant
               | VC_Loop_Invariant
               | VC_Loop_Invariant_Init
               | VC_Loop_Invariant_Preserv
               | VC_Assert
            =>
               return (True,
                       SA_Message'(SA_Messages.Assertion_Check,
                                   Statically_Known_Success));

            when VC_Length_Check
               | VC_Ceiling_Interrupt
               | VC_Interrupt_Reserved
               | VC_Ceiling_Priority_Protocol
               | VC_Task_Termination
               | VC_Raise
               | VC_Weaker_Pre
               | VC_Trivial_Weaker_Pre
               | VC_Stronger_Post
               | VC_Weaker_Classwide_Pre
               | VC_Stronger_Classwide_Post
               | VC_Predicate_Check
               | VC_Predicate_Check_On_Default_Value
               | VC_Invariant_Check
               | VC_Invariant_Check_On_Default_Value
            =>
               return (OK => False);
         end case;
      end Make_Codepeer_Msg;

   --  Start of processing for CodePeer_Has_Proved

   begin
      if CP_File_Present then
         declare
            Opt : constant Opt_Msg := Make_Codepeer_Msg (Kind);
         begin
            if Opt.OK then
               declare
                  Msg : constant Message_And_Location :=
                    Make_Msg_Loc (Loc => Make_CodePeer_Loc (Slc),
                                  Msg => Opt.Msg);
               begin
                  return Codepeer_Proved.Contains (Msg);
               end;
            else
               return False;
            end if;
         end;
      else
         return False;
      end if;
   end CodePeer_Has_Proved;

   -----------------------
   -- Emit_Proof_Result --
   -----------------------

   procedure Emit_Proof_Result
     (Node       : Node_Id;
      Id         : VC_Id;
      Kind       : VC_Kind;
      Proved     : Boolean;
      E          : Entity_Id;
      How_Proved : Prover_Category;
      Extra_Msg  : String := "";
      Tracefile  : String := "";
      Cntexmp    : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      Check_Tree : GNATCOLL.JSON.JSON_Value := GNATCOLL.JSON.Create_Object;
      VC_File    : String := "";
      VC_Loc     : Node_Id := Empty;
      Stats      : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
      Editor_Cmd : String := "") is

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

      Msg : constant String :=
        (if Proved
         then Proved_Message (Node, Kind) & Stat_Message
         else Not_Proved_Message (Node, Kind)) &
              Extra_Msg &
              (if VC_File /= "" then ", vc file: " & VC_File else "");

   --  Start of processing for Emit_Proof_Result

   begin
      if Proved then
         Mark_VC_As_Proved_For_Entity (Id, Kind, E);
      end if;
      Error_Msg_Proof
        (Node,
         Msg,
         Proved,
         Kind,
         Place_First => Locate_On_First_Token (Kind),
         Tracefile   => Tracefile,
         Cntexmp     => Cntexmp,
         Check_Tree  => Check_Tree,
         VC_File     => VC_File,
         VC_Loc      => VC_Loc,
         Editor_Cmd  => Editor_Cmd,
         Stats       => Stats,
         How_Proved  => How_Proved,
         E           => E);
   end Emit_Proof_Result;

   ------------------------
   -- Has_Registered_VCs --
   ------------------------

   function Has_Registered_VCs return Boolean is
     (not VC_Table.Is_Empty);

   ---------------------------
   -- Load_Codepeer_Results --
   ---------------------------

   procedure Load_Codepeer_Results is

      use Reading;
      Base_Name : constant String :=
        Unit_Name & "__body.sam" & SA_Messages.File_Extension;
      File_Name : constant String :=
        Ada.Directories.Compose
          (To_String (Gnat2Why_Args.CP_Res_Dir),
           Base_Name);
   begin
      if Gnat2Why_Args.CP_Res_Dir = Null_Unbounded_String then
         return;
      end if;
      if not Exists (File_Name)
        or else Kind (File_Name) /= Ordinary_File
      then
         return;
      end if;
      CP_File_Present := True;

      --  Opening file with base name and not with full path. We will later
      --  match messages that we construct in gnat2why with the messages that
      --  we parse here, and the former only have basenames.

      Open (File_Name, Full_Path => False);
      while not Done loop
         declare
            Msg : constant Message_And_Location := Get;
         begin
            if Message (Msg).Check_Result = Statically_Known_Success then
               Codepeer_Proved.Include (Msg);
            end if;
         end;
      end loop;
   end Load_Codepeer_Results;

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
            if Nkind (Node) in N_Entry_Call_Statement
                             | N_Procedure_Call_Statement
              and then Is_Error_Signaling_Procedure (Get_Called_Entity (Node))
            then
               declare
                  Subp : constant Entity_Id :=
                    Unique_Entity
                      (Lib.Xref.SPARK_Specific.
                         Enclosing_Subprogram_Or_Library_Package (Node));
               begin
                  if Ekind (Subp) = E_Procedure
                    and then Is_Error_Signaling_Procedure (Subp)
                  then
                     return "precondition might fail";
                  else
                     return
                       "call to nonreturning subprogram might be executed";
                  end if;
               end;
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
            return "loop invariant might fail after first iteration";
         when VC_Loop_Variant              =>
            return "loop variant might fail";
         when VC_Assert                    =>
            return "assertion might fail";
         when VC_Raise                     =>
            return "exception might be raised";

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
      end case;
   end Not_Proved_Message;

   ------------------------
   -- Parse_Why3_Results --
   ------------------------

   procedure Parse_Why3_Results (S : String; Timing : in out Time_Token) is

      --  See the file gnat_report.mli for a description of the format that we
      --  parse here.

      use GNATCOLL.JSON;

      type Why3_Prove_Result is record
         Id         : VC_Id;
         Kind       : VC_Kind;
         Result     : Boolean;
         Extra_Info : Node_Id;
         Tracefile  : Unbounded_String;
         VC_File    : Unbounded_String;
         Editor_Cmd : Unbounded_String;
         Stats      : Prover_Stat_Maps.Map;
         Cntexmp    : JSON_Value;
         Check_Tree : JSON_Value;
      end record;

      function Parse_Why3_Prove_Result (V : JSON_Value)
                                        return Why3_Prove_Result;
      --  parse the JSON produced for Why3 for a single Why3 result record.

      procedure Handle_Result (V : JSON_Value);
      procedure Handle_Error (Msg : String; Internal : Boolean) with No_Return;
      procedure Handle_Timings (V : JSON_Value);

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

      procedure Handle_Result (V : JSON_Value) is
         Rec : constant Why3_Prove_Result := Parse_Why3_Prove_Result (V);
         VC  : constant VC_Info := VC_Table.Element (Rec.Id);
         Extra_Text : constant String :=
           (if not Rec.Result and then Present (Rec.Extra_Info)
            then String_Of_Node (Original_Node (Rec.Extra_Info))
            else "");
         Extra_Msg  : constant String :=
           (if Extra_Text /= "" then ", cannot prove ~" else "");
         Node   : constant Node_Id :=
           (if Present (Rec.Extra_Info) then Rec.Extra_Info else VC.Node);
         --  Extra_info contains the locations of the first failing part of the
         --  VC (which is required in messages). VC_Sloc contains the location
         --  of the check (required in messages for manual provers).
         VC_Sloc    : constant Node_Id := VC.Node;
      begin
         Errout.Error_Msg_String (1 .. Extra_Text'Length) := Extra_Text;
         Errout.Error_Msg_Strlen := Extra_Text'Length;
         Emit_Proof_Result
           (Node        => Node,
            Id          => Rec.Id,
            Kind        => Rec.Kind,
            Proved      => Rec.Result,
            E           => VC.Entity,
            How_Proved  => PC_Prover,
            Tracefile   => To_String (Rec.Tracefile),
            Cntexmp     => Rec.Cntexmp,
            Check_Tree  => Rec.Check_Tree,
            VC_File     => To_String (Rec.VC_File),
            VC_Loc      => VC_Sloc,
            Editor_Cmd  => To_String (Rec.Editor_Cmd),
            Stats       => Rec.Stats,
            Extra_Msg   => Extra_Msg);
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
            External_Timing (Timing, Name, Duration (Time));
         end Timing_Entry;

      --  Start of processing for Handle_Timings

      begin
         Map_JSON_Object (V, Timing_Entry'Access);
      end Handle_Timings;

      -----------------------------
      -- Parse_Why3_Prove_Result --
      -----------------------------

      function Parse_Why3_Prove_Result  (V : JSON_Value)
                                         return Why3_Prove_Result is
      begin
         return Why3_Prove_Result'
           (Id         => VC_Id (Integer'(Get (Get (V, "id")))),
            Kind       => VC_Kind'Value (Get (Get (V, "reason"))),
            Result     => Get (Get (V, "result")),
            Extra_Info => Node_Id (Integer'(Get (Get (V, "extra_info")))),
            Tracefile  =>
            (if Has_Field (V, "tracefile") then Get (Get (V, "tracefile"))
             else Null_Unbounded_String),
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
            Check_Tree =>
              (if Has_Field (V, "check_tree") then Get (V, "check_tree")
               else Create_Object));
      end Parse_Why3_Prove_Result;

   --  Start of processing for Parse_Why3_Results

   begin
      Mark_Subprograms_With_No_VC_As_Proved;
      declare
         File : constant JSON_Value := Read (S, "");
         Results : constant JSON_Array := Get (Get (File, "results"));
      begin
         if Has_Field (File, "error") then
            declare
               Msg : constant String := Get (Get (File, "error"));
               Internal : constant Boolean :=
                 (if Has_Field (File, "internal") then
                       Get (Get (File, "internal"))
                  else False);
            begin
               Handle_Error (Msg, Internal);
            end;
         end if;
         if Has_Field (File, "timings") then
            Handle_Timings (Get (File, "timings"));
         end if;
         for Index in 1 .. Length (Results) loop
            Handle_Result (Get (Results, Index));
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
      when Invalid_JSON_Stream =>
         --  Something bad happened, output gnatwhy3 error as is
         Handle_Error (S, Internal => True);
   end Parse_Why3_Results;

   --------------------
   -- Proved_Message --
   --------------------

   function Proved_Message
     (Node : Node_Id;
      Kind : VC_Kind) return String is
   begin
      case Kind is
         when VC_Division_Check            => return "division check proved";
         when VC_Index_Check               => return "index check proved";
         when VC_Overflow_Check            => return "overflow check proved";
         when VC_FP_Overflow_Check         =>
            return "float overflow check proved";
         when VC_Range_Check               => return "range check proved";
         when VC_Predicate_Check           => return "predicate check proved";
         when VC_Predicate_Check_On_Default_Value =>
            return "predicate check proved on default value";
         when VC_Invariant_Check           => return "invariant check proved";
         when VC_Invariant_Check_On_Default_Value =>
            return "invariant check proved on default value";
         when VC_Length_Check              => return "length check proved";
         when VC_Discriminant_Check        =>
            return "discriminant check proved";
         when VC_Tag_Check                 =>
            return "tag check proved";
         when VC_Ceiling_Interrupt         =>
            return "ceiling priority in Interrupt_Priority proved";
         when VC_Interrupt_Reserved        =>
            return "availability of interrupt proved";
         when VC_Ceiling_Priority_Protocol =>
            return "ceiling priority protocol is respected";
         when VC_Task_Termination          =>
            return "nontermination of task proved";

         when VC_Initial_Condition         =>
            return "initial condition proved";
         when VC_Default_Initial_Condition =>
            return "default initial condition proved";
         when VC_Precondition              =>
            if Nkind (Node) in N_Entry_Call_Statement
                             | N_Procedure_Call_Statement
              and then Is_Error_Signaling_Procedure (Get_Called_Entity (Node))
            then
               declare
                  Subp : constant Entity_Id :=
                    Unique_Entity
                      (Lib.Xref.SPARK_Specific.
                         Enclosing_Subprogram_Or_Library_Package (Node));
               begin
                  if Ekind (Subp) = E_Procedure
                    and then Is_Error_Signaling_Procedure (Subp)
                  then
                     return "precondition proved";
                  else
                     return "call to nonreturning procedure never executed";
                  end if;
               end;
            else
               return "precondition proved";
            end if;
         when VC_Precondition_Main         =>
            return "precondition of main program proved";
         when VC_Postcondition             => return "postcondition proved";
         when VC_Refined_Post              => return "refined post proved";
         when VC_Contract_Case             => return "contract case proved";
         when VC_Disjoint_Contract_Cases   =>
            return "disjoint contract cases proved";
         when VC_Complete_Contract_Cases   =>
            return "complete contract cases proved";
         when VC_Loop_Invariant            =>
            return "loop invariant proved";
         when VC_Loop_Invariant_Init       =>
            return "loop invariant initialization proved";
         when VC_Loop_Invariant_Preserv    =>
            return "loop invariant preservation proved";
         when VC_Loop_Variant              => return "loop variant proved";
         when VC_Assert                    => return "assertion proved";
         when VC_Raise                     =>
            return "raise statement proved unreachable";
         when VC_Weaker_Pre                =>
            return "precondition is weaker than class-wide precondition";
         when VC_Trivial_Weaker_Pre        =>
            return "precondition is always True";
         when VC_Stronger_Post             =>
            return "postcondition is stronger than class-wide postcondition";
         when VC_Weaker_Classwide_Pre      =>
            return "class-wide precondition is weaker than overridden one";
         when VC_Stronger_Classwide_Post   =>
            return "class-wide postcondition is stronger than overridden one";
      end case;
   end Proved_Message;

   -----------------
   -- Register_VC --
   -----------------

   function Register_VC (N : Node_Id; E : Entity_Id) return VC_Id is
      Registered_Id : VC_Id;
   begin
      VC_Table.Append (VC_Info'(N, E));
      Registered_Id := VC_Table.Last_Index;
      Add_Id_To_Entity (Registered_Id, E);
      return Registered_Id;
   end Register_VC;

   ------------------------
   -- Register_VC_Entity --
   ------------------------

   procedure Register_VC_Entity (E : Entity_Id) is
      Position : Ent_Id_Set_Maps.Cursor;
      Dummy : Boolean;
      pragma Unreferenced (Position, Dummy);
   begin
      VC_Set_Table.Insert (Key => E, Position => Position, Inserted => Dummy);
   end Register_VC_Entity;

end Gnat2Why.Error_Messages;
