------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          S P A R K _ R E P O R T                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with Ada.Calendar;
with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Assumptions;           use Assumptions;
with Assumptions.Search;    use Assumptions.Search;
with Assumption_Types;      use Assumption_Types;
with Call;                  use Call;
with Configuration;         use Configuration;
with GNAT.Calendar.Time_IO;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with GPR2.Project.Attribute;
with Gnat2Why_Opts;         use Gnat2Why_Opts;
with Platform;              use Platform;
with Print_Table;           use Print_Table;
with Report_Database;       use Report_Database;
with SPARK2014VSN;          use SPARK2014VSN;
with String_Utils;          use String_Utils;
with System;
with System.Storage_Elements;
with VC_Kinds;              use VC_Kinds;

package body Spark_Report is

   type SPARK_File_Data is record
      File : Unbounded_String;
      Data : JSON_Value;
   end record;

   package SPARK_File_Lists is new
     Ada.Containers.Doubly_Linked_Lists (SPARK_File_Data);

   End_Time : constant String :=
     GNAT.Calendar.Time_IO.Image
       (Date      => Ada.Calendar.Clock,
        Picture   => "%Y-%m-%dT%H:%M:%SZ",
        Time_Zone => 0);
   --  End time of analysis, used for the reports. Time zone "0" is UTC

   procedure Generate_SARIF_Report
     (Filename           : String;
      SPARK_Files        : SPARK_File_Lists.List;
      Command_Line_Image : String;
      Error_Code         : Integer;
      Tree               : GPR2.Project.Tree.Object);

   ---------------------
   -- Generate_Report --
   ---------------------

   procedure Generate_Report
     (Tree        : GPR2.Project.Tree.Object;
      Out_Dir     : String;
      SPARK_Files : String_Lists.List;
      Has_Errors  : Boolean;
      Status      : out Integer)
   is
      SPARK_Mode_OK : Boolean := False;
      --  This variable is set to True when at least one subprogram was
      --  analyzed as being in SPARK.

      Max_Progress       : Analysis_Progress := Progress_None;
      Error_Code         : Integer := 0;
      Handle             : Ada.Text_IO.File_Type;
      Command_Line_Image : Unbounded_String;

      --  Config values from Configuration/CL_Switches
      Assumptions        : constant Boolean := CL_Switches.Assumptions;
      Output_Header      : constant Boolean := CL_Switches.Output_Header;
      Has_Limit_Switches : constant Boolean :=
        not Null_Or_Empty_String (CL_Switches.Limit_Name)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Subp)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Line)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Lines)
        or else not Null_Or_Empty_String (CL_Switches.Limit_Region);
      Colors             : constant Boolean :=
        Configuration.Output = GPO_Pretty_Color;

      Parsed_Files : SPARK_File_Lists.List;
      --  Subset of SPARK_Files that actually exist on disk, with parsed JSON

      procedure Handle_SPARK_File (Fn : String; Dict : JSON_Value);
      --  Extract all information from a single SPARK file

      procedure Handle_Flow_Items (V : JSON_Array; Unit : Unit_Type);
      --  Parse and extract all information from a flow result array

      procedure Handle_Pragma_Assume_Items (V : JSON_Array; Unit : Unit_Type);
      --  Parse and extract all information from a pragma assume result array

      procedure Handle_Proof_Items (V : JSON_Array; Unit : Unit_Type);
      --  Parse and extract all information from a proof result array

      procedure Handle_Assume_Items (V : JSON_Array; Unit : Unit_Type);
      --  Parse and extract all information from an assume result array

      procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type);
      --  Print the proof report in the given file

      procedure Print_Max_Steps (Handle : Ada.Text_IO.File_Type);
      --  Print a line that summarizes the maximum required steps

      procedure Print_Most_Difficult_Proved_Checks
        (Handle : Ada.Text_IO.File_Type);
      --  Print the set of most difficult checks to prove

      procedure Compute_Assumptions;
      --  Compute remaining assumptions for all subprograms and store them
      --  in database.

      function To_String (Sloc : My_Sloc) return String;
      --  Pretty-printing of slocs including instantiation chains

      procedure Dump_Summary_Table (Handle : Ada.Text_IO.File_Type);
      --  Print the summary table to a file

      procedure Increment (X : in out Integer);
      --  Increment X by 1

      function VC_Kind_To_Summary (S : VC_Kind) return Possible_Entries;
      --  Return the summary entry corresponding to VC kind S

      function Flow_Kind_To_Summary
        (S : Flow_Tag_Kind) return Possible_Entries;
      --  Return the summary entry corresponding to Flow kind S

      function To_String (S : Summary_Entries) return String;
      --  Return the string for a summary table row label

      procedure Process_Stats
        (C         : Summary_Entries;
         Stats     : Prover_Stat_Maps.Map;
         Max_Steps : out Natural;
         Max_Time  : out Float);
      --  Process the stats record for the VC and update proof information

      procedure Show_Header
        (Handle : Ada.Text_IO.File_Type; Command_Line_Image : String);
      --  Print header at start of generated file "gnatprove.out"

      -------------------------
      -- Compute_Assumptions --
      -------------------------

      procedure Compute_Assumptions is
      begin
         --  ??? This is slow, use a better algorithm in Assumptions.Search

         for C of Get_All_Claims loop
            declare
               S : constant Token_Sets.Set := Claim_Depends_On (C);
            begin
               Add_Claim_With_Assumptions (C, S);
            end;
         end loop;
      end Compute_Assumptions;

      ------------------------
      -- Dump_Summary_Table --
      ------------------------

      procedure Dump_Summary_Table (Handle : Ada.Text_IO.File_Type) is

         T : Table :=
           Create_Table
             (Lines =>
                Summary_Entries'Pos (Summary_Entries'Last)
                - Summary_Entries'Pos (Summary_Entries'First)
                + 2,
              --  all categories (includes total) + label column
              Cols  => 4 + 2);
         --  all 5 types + label column + total column

         procedure Print_Table_Header;
         --  Print the header of the table

         procedure Print_Table_Line (Line : Summary_Entries);
         --  Print a line of the table other than the header and the total line

         procedure Print_Table_Total;
         --  Print the "Total" line of the table

         procedure Put_Provers_Cell (Stats : in out All_Prover_Stat);
         --  Print the "provers" cell of a category

         procedure Put_Total_Cell (Part, Total : Natural);
         --  Print a number cell with percentage

         procedure Compute_Total_Summary_Line;
         --  Compute the numbers for the "Total" line of the summary table

         function Integer_Percent (Part, Total : Integer) return Integer
         with Post => Integer_Percent'Result in 0 .. 100;
         --  Compute the percentage of Part in Total

         --------------------------------
         -- Compute_Total_Summary_Line --
         --------------------------------

         procedure Compute_Total_Summary_Line is
            Tot : Summary_Line renames Summary (Total);
         begin
            for Entr in Summary_Entries loop
               if Entr /= Total then
                  Tot.Flow := Tot.Flow + Summary (Entr).Flow;
                  Tot.Provers.Total :=
                    Tot.Provers.Total + Summary (Entr).Provers.Total;
                  Tot.Justified := Tot.Justified + Summary (Entr).Justified;
                  Tot.Unproved := Tot.Unproved + Summary (Entr).Unproved;
               end if;
            end loop;
         end Compute_Total_Summary_Line;

         ---------------------
         -- Integer_Percent --
         ---------------------

         function Integer_Percent (Part, Total : Integer) return Integer is
         begin
            return Integer ((Float (100 * Part)) / Float (Total));
         end Integer_Percent;

         ------------------------
         -- Print_Table_Header --
         ------------------------

         procedure Print_Table_Header is
         begin
            Put_Cell (T, "SPARK Analysis results", Align => Left_Align);
            Put_Cell (T, "Total");
            Put_Cell (T, "Flow");
            Put_Cell (T, "Provers");
            Put_Cell (T, "Justified");
            Put_Cell (T, "Unproved");
            New_Line (T);
         end Print_Table_Header;

         ----------------------
         -- Print_Table_Line --
         ----------------------

         procedure Print_Table_Line (Line : Summary_Entries) is
            Elt   : Summary_Line renames Summary (Line);
            Total : constant Natural :=
              Elt.Flow + Elt.Provers.Total + Elt.Justified + Elt.Unproved;
         begin
            Put_Cell (T, To_String (Line), Align => Left_Align);
            Put_Cell (T, Total);
            Put_Cell (T, Elt.Flow);
            Put_Provers_Cell (Elt.Provers);
            Put_Cell (T, Elt.Justified);
            Put_Cell (T, Elt.Unproved);
            New_Line (T);
         end Print_Table_Line;

         -----------------------
         -- Print_Table_Total --
         -----------------------

         procedure Print_Table_Total is
            Elt : Summary_Line renames Summary (Total);
            Tot : constant Natural :=
              Elt.Flow + Elt.Provers.Total + Elt.Justified + Elt.Unproved;
         begin
            Put_Cell (T, To_String (Total), Align => Left_Align);
            Put_Cell (T, Tot);
            Put_Total_Cell (Elt.Flow, Tot);
            Put_Total_Cell (Elt.Provers.Total, Tot);
            Put_Total_Cell (Elt.Justified, Tot);
            Put_Total_Cell (Elt.Unproved, Tot);
            New_Line (T);
         end Print_Table_Total;

         ----------------------
         -- Put_Provers_Cell --
         ----------------------

         procedure Put_Provers_Cell (Stats : in out All_Prover_Stat) is
            use Prover_Stat_Maps;
            use Ada.Containers;
            Check_Total : constant Natural := Stats.Total;
            VC_Total    : Natural := 0;
            Buf         : Unbounded_String;
            First       : Boolean := True;
         begin
            if Check_Total = 0 or else Stats.Provers.Is_Empty then
               Put_Cell (T, Check_Total);
               return;
            end if;
            Append (Buf, Natural'Image (Check_Total));
            for Elt of Stats.Provers loop
               VC_Total := VC_Total + Elt.Count;
            end loop;
            for Elt of Stats.Provers loop
               Elt.Count := Integer_Percent (Elt.Count, VC_Total);
            end loop;
            Append (Buf, " (");
            if Stats.Provers.Length = 1 then
               Append (Buf, Key (Stats.Provers.First));
            else
               for C in Stats.Provers.Iterate loop
                  if not First then
                     Append (Buf, ", ");
                  end if;
                  First := False;
                  Append (Buf, Key (C));
                  Append (Buf, Natural'Image (Element (C).Count) & "%");
               end loop;
            end if;
            Append (Buf, ')');
            Put_Cell (T, To_String (Buf));
         end Put_Provers_Cell;

         --------------------
         -- Put_Total_Cell --
         --------------------

         procedure Put_Total_Cell (Part, Total : Natural) is
         begin
            if Part = 0 then
               Put_Cell (T, 0);
            else
               declare
                  Pcnt_Img : constant String :=
                    Integer'Image (Integer_Percent (Part, Total));
                  No_Space : String renames
                    Pcnt_Img (Pcnt_Img'First + 1 .. Pcnt_Img'Last);
               begin
                  Put_Cell (T, Integer'Image (Part) & " (" & No_Space & "%)");
               end;
            end if;
         end Put_Total_Cell;

      begin
         Compute_Total_Summary_Line;
         Ada.Text_IO.Put_Line (Handle, "=========================");
         Ada.Text_IO.Put_Line (Handle, "Summary of SPARK analysis");
         Ada.Text_IO.Put_Line (Handle, "=========================");
         Ada.Text_IO.New_Line (Handle);
         Print_Table_Header;
         for Line in Summary_Entries loop
            if Line = Total then
               Print_Table_Total;
            else
               Print_Table_Line (Line);
            end if;
         end loop;
         Dump_Table (Handle, T);
      end Dump_Summary_Table;

      --------------------------
      -- Flow_Kind_To_Summary --
      --------------------------

      function Flow_Kind_To_Summary (S : Flow_Tag_Kind) return Possible_Entries
      is
      begin
         case S is
            when Empty_Tag                                             =>
               return No_Entry;

            when Aliasing                                              =>
               return Non_Aliasing;

            when Call_To_Current_Task                                  =>
               return Runtime_Checks;

            when Concurrent_Access | Potentially_Blocking_In_Protected =>
               return Concurrency;

            when Critical_Global_Missing
               | Global_Missing
               | Global_Wrong
               | Export_Depends_On_Proof_In
               | Ghost_Wrong
               | Hidden_Unexposed_State
               | Illegal_Update
               | Non_Volatile_Function_With_Volatile_Effects
               | Refined_State_Wrong
               | Side_Effects
               | Unused_Global                                         =>
               return Data_Dep;

            when Impossible_To_Initialize_State
               | Initializes_Wrong
               | Uninitialized
               | Default_Initialization_Mismatch                       =>
               return Init;

            when Depends_Missing
               | Depends_Missing_Clause
               | Depends_Null
               | Depends_Wrong                                         =>
               return Flow_Dep;

            when Call_In_Type_Invariant | Subprogram_Termination       =>
               return Termination;

            when Dead_Code
               | Ineffective
               | Inout_Only_Read
               | Missing_Return
               | Not_Constant_After_Elaboration
               | Reference_To_Non_CAE_Variable
               | Stable
               | Unused_Initial_Value
               | Unused_Variable                                       =>
               return No_Entry;
         end case;
      end Flow_Kind_To_Summary;

      -------------------------
      -- Handle_Assume_Items --
      -------------------------

      procedure Handle_Assume_Items (V : JSON_Array; Unit : Unit_Type) is
         pragma Unreferenced (Unit);
         RL : constant Rule_Lists.List := From_JSON (V);
      begin
         Import (RL);
      end Handle_Assume_Items;

      -----------------------
      -- Handle_Flow_Items --
      -----------------------

      procedure Handle_Flow_Items (V : JSON_Array; Unit : Unit_Type) is

         function Severity_To_Msg_Kind (S : String) return Flow_Message_Kind;

         --------------------------
         -- Severity_To_Msg_Kind --
         --------------------------

         function Severity_To_Msg_Kind (S : String) return Flow_Message_Kind is
         begin
            if S = "error" then
               return FMK_Error;
            elsif S = "warning" then
               return FMK_Warning;
            elsif S = "high" or else S = "medium" or else S = "low" then
               return FMK_Check;
            else
               Ada.Text_IO.Put_Line ("severity: " & S);
               raise Program_Error;
            end if;
         end Severity_To_Msg_Kind;

         --  Start of Processing for Handle_Flow_Items

      begin
         for Index in 1 .. Length (V) loop
            declare
               Result   : constant JSON_Value := Get (V, Index);
               Severe   : constant String := Get (Get (Result, "severity"));
               Subp     : constant Subp_Type :=
                 From_JSON (Get (Result, "entity"));
               Kind     : constant Flow_Tag_Kind :=
                 Flow_Tag_Kind'Value (Get (Get (Result, "rule")));
               Category : constant Possible_Entries :=
                 Flow_Kind_To_Summary (Kind);
            begin
               if Has_Field (Result, "suppressed") then
                  if Severe /= "warning" then
                     Add_Suppressed_Check
                       (Unit       => Unit,
                        Subp       => Subp,
                        Justif_Msg => Get (Get (Result, "justif_msg")),
                        Kind       => Get (Get (Result, "annot_kind")),
                        Reason     => Get (Get (Result, "suppressed")),
                        File       => Get (Get (Result, "file")),
                        Line       => Get (Get (Result, "line")),
                        Column     => Get (Get (Result, "col")));
                     if Category /= No_Entry then
                        Increment (Summary (Category).Justified);
                     end if;
                  end if;
               elsif Severe = "info" then
                  if Category /= No_Entry then
                     Increment (Summary (Category).Flow);
                  end if;
               else
                  Add_Flow_Result
                    (Unit     => Unit,
                     Subp     => Subp,
                     Msg_Kind => Severity_To_Msg_Kind (Severe));
                  if Category /= No_Entry then
                     Increment (Summary (Category).Unproved);
                  end if;
               end if;
            end;
         end loop;
      end Handle_Flow_Items;

      --------------------------------
      -- Handle_Pragma_Assume_Items --
      --------------------------------

      procedure Handle_Pragma_Assume_Items (V : JSON_Array; Unit : Unit_Type)
      is
      begin
         for Index in 1 .. Length (V) loop
            declare
               Result : constant JSON_Value := Get (V, Index);
               File   : constant String := Get (Result, "file");
               Line   : constant Positive := Get (Result, "line");
               Column : constant Positive := Get (Result, "col");
               Subp   : constant Subp_Type :=
                 From_JSON (Get (Result, "entity"));
            begin
               Add_Pragma_Assume_Result
                 (Unit   => Unit,
                  File   => File,
                  Line   => Line,
                  Column => Column,
                  Subp   => Subp);
            end;
         end loop;
      end Handle_Pragma_Assume_Items;

      ------------------------
      -- Handle_Proof_Items --
      ------------------------

      procedure Handle_Proof_Items (V : JSON_Array; Unit : Unit_Type) is
      begin
         for Index in 1 .. Length (V) loop
            declare
               Result   : constant JSON_Value := Get (V, Index);
               Severe   : constant String := Get (Get (Result, "severity"));
               Kind     : constant VC_Kind :=
                 VC_Kind'Value (Get (Get (Result, "rule")));
               Subp     : constant Subp_Type :=
                 From_JSON (Get (Result, "entity"));
               Category : constant Possible_Entries :=
                 VC_Kind_To_Summary (Kind);
               Proved   : constant Boolean := Severe = "info";
               File     : constant String := Get (Get (Result, "file"));
               Line     : constant Positive := Get (Get (Result, "line"));
               Column   : constant Positive := Get (Get (Result, "col"));
            begin
               if Category = Warnings then
                  null;
               elsif Has_Field (Result, "suppressed") then
                  Increment (Summary (Category).Justified);
                  Add_Suppressed_Check
                    (Unit       => Unit,
                     Subp       => Subp,
                     Justif_Msg => Get (Get (Result, "justif_msg")),
                     Kind       => Get (Get (Result, "annot_kind")),
                     Reason     => Get (Get (Result, "suppressed")),
                     File       => File,
                     Line       => Line,
                     Column     => Column);
               else
                  Add_Proof_Result
                    (Unit => Unit, Subp => Subp, Proved => Proved);
                  if Proved then
                     declare
                        Cat : constant Prover_Category :=
                          From_JSON (Get (Result, "how_proved"));
                     begin
                        case Cat is
                           when PC_Trivial =>
                              declare
                                 M : Prover_Stat_Maps.Map;
                              begin
                                 M.Insert
                                   ("Trivial",
                                    Prover_Stat'
                                      (Count     => 1,
                                       Max_Steps => 1,
                                       Max_Time  => 0.0));
                                 Merge_Stat_Maps
                                   (Summary (Category).Provers.Provers, M);
                                 Increment (Summary (Category).Provers.Total);
                              end;

                           when PC_Prover  =>
                              if Has_Field (Result, "stats") then
                                 declare
                                    Stats     :
                                      constant Prover_Stat_Maps.Map :=
                                        From_JSON (Get (Result, "stats"));
                                    Max_Steps : Natural;
                                    Max_Time  : Float;
                                 begin
                                    Process_Stats
                                      (Category, Stats, Max_Steps, Max_Time);

                                    Update_Most_Difficult_Proved_Checks
                                      (Proved_Check'
                                         (Unit      => Unit,
                                          Subp      => Subp,
                                          Kind      => Kind,
                                          File      =>
                                            To_Unbounded_String (File),
                                          Line      => Line,
                                          Column    => Column,
                                          Max_Steps => Max_Steps,
                                          Max_Time  => Max_Time));
                                 end;
                              end if;
                              Increment (Summary (Category).Provers.Total);

                           when PC_Flow    =>
                              --  we shouldn't encounter flow values here
                              raise Program_Error;
                        end case;
                     end;
                  else
                     Increment (Summary (Category).Unproved);
                  end if;
               end if;
            end;
         end loop;
      end Handle_Proof_Items;

      -----------------------
      -- Handle_SPARK_File --
      -----------------------

      procedure Handle_SPARK_File (Fn : String; Dict : JSON_Value) is

         Basename : constant String := Ada.Directories.Base_Name (Fn);
         Unit     : constant Unit_Type := Mk_Unit (Basename);

         procedure Handle_SPARK_Status
           (Name : UTF8_String; Value : JSON_Value);
         --  Handle one entry of the "spark" status map

         -------------------------
         -- Handle_SPARK_Status --
         -------------------------

         procedure Handle_SPARK_Status (Name : UTF8_String; Value : JSON_Value)
         is
            SPARK_Status : constant SPARK_Mode_Status := From_JSON (Value);
         begin
            Add_SPARK_Status
              (Unit         => Unit,
               Subp         => From_Key (Name),
               SPARK_Status => SPARK_Status);

            if SPARK_Status = All_In_SPARK then
               SPARK_Mode_OK := True;
            end if;

         end Handle_SPARK_Status;

         Has_Flow    : constant Boolean := Has_Field (Dict, "flow");
         Has_Assumes : constant Boolean := Has_Field (Dict, "pragma_assume");
         Has_Proof   : constant Boolean := Has_Field (Dict, "proof");

         Analysis    : constant Analysis_Progress :=
           Analysis_Progress'Value (String'(Get (Dict, "progress")));
         Stop_Reason : constant Stop_Reason_Type :=
           Stop_Reason_Type'Value (String'(Get (Dict, "stop_reason")));

         SPARK_Status_Dict        : constant JSON_Value := Get (Dict, "spark");
         Skip_Flow_And_Proof_List : constant JSON_Array :=
           Get (Dict, "skip_flow_proof");
         Skip_Proof_List          : constant JSON_Array :=
           Get (Dict, "skip_proof");
      begin
         Parse_Entity_Table (Get (Dict, "entities"));
         Add_Analysis_Progress (Unit, Analysis, Stop_Reason);
         Map_JSON_Object (SPARK_Status_Dict, Handle_SPARK_Status'Access);
         for Index in 1 .. Length (Skip_Flow_And_Proof_List) loop
            Add_Skip_Flow_And_Proof
              (From_JSON (Get (Skip_Flow_And_Proof_List, Index)));
         end loop;
         for Index in 1 .. Length (Skip_Proof_List) loop
            Add_Skip_Proof (From_JSON (Get (Skip_Proof_List, Index)));
         end loop;
         Max_Progress := Analysis_Progress'Max (Max_Progress, Analysis);
         if Has_Flow then
            Handle_Flow_Items (Get (Get (Dict, "flow")), Unit);
         end if;
         if Has_Assumes then
            Handle_Pragma_Assume_Items
              (Get (Get (Dict, "pragma_assume")), Unit);
         end if;
         if Has_Proof then
            Handle_Proof_Items (Get (Get (Dict, "proof")), Unit);
         end if;
         if Assumptions and then Has_Field (Dict, "assumptions") then
            Handle_Assume_Items (Get (Get (Dict, "assumptions")), Unit);
         end if;
      end Handle_SPARK_File;

      ---------------
      -- Increment --
      ---------------

      procedure Increment (X : in out Integer) is
      begin
         X := X + 1;
      end Increment;

      ---------------------------
      -- Print_Analysis_Report --
      ---------------------------

      procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type) is
         use Ada.Text_IO;

         function To_String (Reason : Stop_Reason_Type) return String;
         --  Produce human readable string for the stop reason

         procedure For_Each_Unit (Unit : Unit_Type);
         --  print proof results for the given unit

         -------------------
         -- For_Each_Unit --
         -------------------

         procedure For_Each_Unit (Unit : Unit_Type) is

            procedure For_Each_Subp
              (Subp     : Subp_Type;
               Stat     : Stat_Rec;
               Analysis : Analysis_Progress);

            -------------------
            -- For_Each_Subp --
            -------------------

            procedure For_Each_Subp
              (Subp : Subp_Type; Stat : Stat_Rec; Analysis : Analysis_Progress)
            is
            begin
               Put
                 (Handle,
                  "  "
                  & Subp_Name (Subp)
                  & " at "
                  & To_String (Subp_Sloc (Subp)));

               if Stat.SPARK = All_In_SPARK then
                  if Analysis < Progress_Flow then
                     Put_Line (Handle, " not analyzed");
                  elsif Has_Skip_Flow_And_Proof (Subp) then
                     Put_Line
                       (Handle,
                        " not analyzed"
                        & " (pragma Annotate Skip_Flow_And_Proof)");
                  else
                     Put
                       (Handle,
                        " flow analyzed ("
                        & Image (Stat.Flow_Errors, 1)
                        & " errors, "
                        & Image (Stat.Flow_Checks, 1)
                        & " checks, "
                        & Image (Stat.Flow_Warnings, 1)
                        & " warnings and "
                        & Image (Natural (Stat.Pragma_Assumes.Length), 1)
                        & " pragma Assume "
                        & "statements)");

                     if Analysis = Progress_Proof then
                        if Has_Skip_Proof (Subp) then
                           Put
                             (Handle,
                              ", proof skipped"
                              & " (pragma Annotate Skip_Proof)");
                        else
                           Put (Handle, " and");
                           if Stat.Proof_Checks = Stat.Proof_Checks_OK then
                              Put
                                (Handle,
                                 " proved ("
                                 & Image (Stat.Proof_Checks, 1)
                                 & " checks)");
                           else
                              Put
                                (Handle,
                                 " not proved,"
                                 & Stat.Proof_Checks_OK'Img
                                 & " checks out of"
                                 & Stat.Proof_Checks'Img
                                 & " proved");
                           end if;
                        end if;
                     end if;

                     Put_Line (Handle, "");

                     if not Stat.Suppr_Checks.Is_Empty then
                        Put_Line (Handle, "   Justified check messages:");
                        for Msg of Stat.Suppr_Checks loop
                           declare
                              Marked_As : constant Unbounded_String :=
                                " (marked as: " & Msg.Kind;

                              Reason : constant Unbounded_String :=
                                "reason: """ & Msg.Reason & """)";

                              Explanation : constant Unbounded_String :=
                                Marked_As & ", " & Reason;

                           begin
                              Put_Line
                                (Handle,
                                 "    "
                                 & To_String (Msg.File)
                                 & ":"
                                 & Image (Msg.Line, 1)
                                 & ":"
                                 & Image (Msg.Column, 1)
                                 & ":"
                                 & (if Msg.Justif_Msg /= ""
                                    then " " & To_String (Msg.Justif_Msg)
                                    else "")
                                 & To_String (Explanation));
                           end;
                        end loop;
                     end if;

                     if not Stat.Pragma_Assumes.Is_Empty then
                        Put_Line (Handle, "   pragma Assume statements:");
                        for Assm of Stat.Pragma_Assumes loop
                           Put_Line
                             (Handle,
                              "    "
                              & Ada.Strings.Unbounded.To_String (Assm.File)
                              & ":"
                              & Image (Assm.Line, 1)
                              & ":"
                              & Image (Assm.Column, 1));
                        end loop;
                     end if;

                     if Assumptions then
                        for Rule of Stat.Assumptions loop
                           if Rule.Assumptions.Is_Empty then
                              Ada.Text_IO.Put_Line
                                (Handle,
                                 To_String (Rule.Claim)
                                 & " fully established");
                           else
                              Ada.Text_IO.Put_Line
                                (Handle,
                                 To_String (Rule.Claim) & " depends on");
                              for A of Rule.Assumptions loop
                                 Ada.Text_IO.Put_Line
                                   (Handle, "  " & To_String (A));
                              end loop;
                           end if;
                        end loop;
                     end if;
                  end if;

               else
                  Put (Handle, " skipped; ");
                  if Stat.SPARK = Not_In_SPARK then
                     Put_Line (Handle, "SPARK_Mode => Off");
                  else
                     Put_Line (Handle, "body is SPARK_Mode => Off");
                  end if;
               end if;
            end For_Each_Subp;

         begin
            Put_Line
              (Handle,
               "in unit "
               & Unit_Name (Unit)
               & ", "
               & Image (Num_Subps_SPARK (Unit), 1)
               & " subprograms and packages out of "
               & Image (Num_Subps (Unit), 1)
               & " analyzed");

            if Unit_Progress (Unit) < Progress_Flow then
               Put (Handle, "flow analysis and ");
            end if;
            if Unit_Progress (Unit) < Progress_Proof then
               Put (Handle, "proof skipped for this unit");
               if Unit_Stop_Reason (Unit) = Stop_Reason_None then
                  New_Line (Handle);
               else
                  Put (Handle, " (");
                  Put (Handle, To_String (Unit_Stop_Reason (Unit)));
                  Put_Line (Handle, ")");
               end if;
            end if;

            Iter_Unit_Subps (Unit, For_Each_Subp'Access, Ordered => True);

         end For_Each_Unit;

         ---------------
         -- To_String --
         ---------------

         function To_String (Reason : Stop_Reason_Type) return String is
         begin
            case Reason is
               when Stop_Reason_None          =>
                  return "";

               when Stop_Reason_Generic_Unit  =>
                  return "generic unit is not analyzed";

               when Stop_Reason_Check_Mode    =>
                  return "only SPARK_Mode checking was requested";

               when Stop_Reason_Flow_Mode     =>
                  return "only flow analysis was requested";

               when Stop_Reason_Error_Marking =>
                  return "error during checking of SPARK_Mode";

               when Stop_Reason_Error_Flow    =>
                  return "error during flow analysis";

               when Stop_Reason_Error_Borrow  =>
                  return "error during ownership checking";
            end case;
         end To_String;

         N : constant Natural := Num_Units;

         Unit_Str : constant String := (if N = 1 then "unit" else "units");

      begin
         Ada.Text_IO.Put_Line (Handle, "========================");
         Ada.Text_IO.Put_Line (Handle, "Detailed analysis report");
         Ada.Text_IO.Put_Line (Handle, "========================");
         Ada.Text_IO.New_Line (Handle);

         if N > 0 then
            Put_Line (Handle, "Analyzed" & N'Img & " " & Unit_Str);
            Iter_Units (For_Each_Unit'Access, Ordered => True);
         end if;
      end Print_Analysis_Report;

      ---------------------
      -- Print_Max_Steps --
      ---------------------

      procedure Print_Max_Steps (Handle : Ada.Text_IO.File_Type) is
         Map : Prover_Stat_Maps.Map := Prover_Stat_Maps.Empty_Map;
         Max : Natural := 0;
      begin
         for Elt of Summary loop
            Merge_Stat_Maps (Map, Elt.Provers.Provers);
         end loop;

         for Elt of Map loop
            if Elt.Max_Steps > Max then
               Max := Elt.Max_Steps;
            end if;
         end loop;
         Ada.Text_IO.Put_Line
           (Handle,
            "max steps used for successful proof:" & Natural'Image (Max));
         Ada.Text_IO.New_Line (Handle);
      end Print_Max_Steps;

      ----------------------------------------
      -- Print_Most_Difficult_Proved_Checks --
      ----------------------------------------

      procedure Print_Most_Difficult_Proved_Checks
        (Handle : Ada.Text_IO.File_Type)
      is
         Found_One : Boolean := False;
      begin
         Ada.Text_IO.Put_Line (Handle, "============================");
         Ada.Text_IO.Put_Line (Handle, "Most difficult proved checks");
         Ada.Text_IO.Put_Line (Handle, "============================");
         Ada.Text_IO.New_Line (Handle);

         for PC of reverse Most_Difficult_Proved_Checks loop
            declare
               Max_Time : constant Natural := Integer (PC.Max_Time);
            begin
               if Max_Time > 0 then
                  Found_One := True;
                  Ada.Text_IO.Put_Line
                    (Handle,
                     f"{To_String (PC.File)}:{PC.Line}:{PC.Column}: "
                     & f"{Kind_Name (PC.Kind)} proved in max {Max_Time}"
                     & " seconds");
               end if;
            end;
         end loop;

         if not Found_One then
            Ada.Text_IO.Put_Line
              (Handle, "No check found with max time greater than 1 second");
         end if;

         Ada.Text_IO.New_Line (Handle);
      end Print_Most_Difficult_Proved_Checks;

      -------------------
      -- Process_Stats --
      -------------------

      procedure Process_Stats
        (C         : Summary_Entries;
         Stats     : Prover_Stat_Maps.Map;
         Max_Steps : out Natural;
         Max_Time  : out Float) is
      begin
         Merge_Stat_Maps (Summary (C).Provers.Provers, Stats);

         Max_Steps := 0;
         Max_Time := 0.0;

         for PS of Stats loop
            Max_Steps := Natural'Max (Max_Steps, PS.Max_Steps);
            Max_Time := Float'Max (Max_Time, PS.Max_Time);
         end loop;
      end Process_Stats;

      -----------------
      -- Show_Header --
      -----------------

      procedure Show_Header
        (Handle : Ada.Text_IO.File_Type; Command_Line_Image : String)
      is
         use Ada.Text_IO;

         function OS_String return String;
         --  Return a nice string for the OS GNATprove was compiled for

         ---------------
         -- OS_String --
         ---------------

         function OS_String return String
         is (case Get_OS_Flavor is
               when X86_Windows | X86_64_Windows             => "Windows",
               when X86_Linux | X86_64_Linux | AArch64_Linux => "Linux",
               when X86_64_Darwin                            => "Darwin",
               when X86_64_FreeBSD                           => "FreeBSD",
               when GNATSAS_OS                               => "GNATSAS OS",
               when AArch64_Darwin                           => "Darwin");

         Pointer_Size : constant :=
           System.Storage_Elements.Integer_Address'Size / System.Storage_Unit;

      begin
         Put_Line (Handle, "date               : " & End_Time);
         Put_Line (Handle, "gnatprove version  : " & SPARK2014_Version_String);
         Put_Line
           (Handle,
            "host               : "
            & OS_String
            & Integer'Image (Pointer_Size * 8)
            & " bits");

         Put_Line (Handle, "command line       : " & Command_Line_Image);

         --  Switches attribute from project
         declare
            Attr : constant GPR2.Project.Attribute.Object :=
              Tree.Root_Project.Attribute ((+"Prove", +"Switches"));
         begin
            if Attr.Is_Defined then
               declare
                  Buf   : Unbounded_String;
                  First : Boolean := True;
               begin
                  for V of Attr.Values loop
                     if not First then
                        Append (Buf, ' ');
                     end if;
                     First := False;
                     Append (Buf, String (V.Text));
                  end loop;
                  Put_Line (Handle, "Switches attribute: " & To_String (Buf));
               end;
            end if;
         end;

         --  Proof_Switches attribute from project
         declare
            Has_Any : Boolean := False;
         begin
            for Attr of
              Tree.Root_Project.Attributes ((+"Prove", +"Proof_Switches"))
            loop
               if not Has_Any then
                  Put_Line (Handle, " Proof_Switches attribute:");
                  Has_Any := True;
               end if;
               declare
                  Buf   : Unbounded_String;
                  First : Boolean := True;
               begin
                  for V of Attr.Values loop
                     if not First then
                        Append (Buf, ' ');
                     end if;
                     First := False;
                     Append (Buf, String (V.Text));
                  end loop;
                  Put_Line
                    (Handle,
                     "   "
                     & String (Attr.Index.Text)
                     & ": "
                     & To_String (Buf));
               end;
            end loop;
         end;
      end Show_Header;

      ---------------
      -- To_String --
      ---------------

      function To_String (Sloc : My_Sloc) return String is
         First  : Boolean := True;
         Result : Unbounded_String;
      begin
         for S of Sloc loop
            if not First then
               Append (Result, ", instantiated at ");
            else
               First := False;
            end if;
            Append (Result, Base_Sloc_File (S));
            Append (Result, ':');
            Append (Result, Image (S.Line, 1));
         end loop;
         return To_String (Result);
      end To_String;

      function To_String (S : Summary_Entries) return String is
      begin
         case S is
            when Data_Dep             =>
               return "Data Dependencies";

            when Flow_Dep             =>
               return "Flow Dependencies";

            when Init                 =>
               return "Initialization";

            when Non_Aliasing         =>
               return "Non-Aliasing";

            when Runtime_Checks       =>
               return "Run-time Checks";

            when Assertions           =>
               return "Assertions";

            when Functional_Contracts =>
               return "Functional Contracts";

            when LSP                  =>
               return "LSP Verification";

            when Termination          =>
               return "Termination";

            when Concurrency          =>
               return "Concurrency";

            when Total                =>
               return "Total";
         end case;
      end To_String;

      ------------------------
      -- VC_Kind_To_Summary --
      ------------------------

      function VC_Kind_To_Summary (S : VC_Kind) return Possible_Entries is
      begin
         case S is
            when VC_Division_Check
               | VC_Index_Check
               | VC_Overflow_Check
               | VC_FP_Overflow_Check
               | VC_Range_Check
               | VC_Predicate_Check
               | VC_Predicate_Check_On_Default_Value
               | VC_Invariant_Check
               | VC_Invariant_Check_On_Default_Value
               | VC_Null_Pointer_Dereference
               | VC_Null_Exclusion
               | VC_Dynamic_Accessibility_Check
               | VC_Resource_Leak
               | VC_Resource_Leak_At_End_Of_Scope
               | VC_Length_Check
               | VC_Discriminant_Check
               | VC_Tag_Check
               | VC_Ceiling_Interrupt
               | VC_Interrupt_Reserved
               | VC_Ceiling_Priority_Protocol
               | VC_Task_Termination
               | VC_Raise
               | VC_Unexpected_Program_Exit
               | VC_UC_Source
               | VC_UC_Target
               | VC_UC_Same_Size
               | VC_UC_Align_Overlay
               | VC_UC_Align_UC
               | VC_Unchecked_Union_Restriction
               | VC_UC_Volatile
               | VC_Validity_Check
            =>
               return Runtime_Checks;

            when VC_Initialization_Check
            =>
               return Init;

            when VC_Assert
               | VC_Assert_Premise
               | VC_Assert_Step
               | VC_Loop_Invariant
               | VC_Loop_Invariant_Init
               | VC_Loop_Invariant_Preserv
            =>
               return Assertions;

            when VC_Loop_Variant | VC_Subprogram_Variant | VC_Termination_Check
            =>
               return Termination;

            when VC_Initial_Condition
               | VC_Default_Initial_Condition
               | VC_Precondition
               | VC_Precondition_Main
               | VC_Postcondition
               | VC_Refined_Post
               | VC_Contract_Case
               | VC_Disjoint_Cases
               | VC_Complete_Cases
               | VC_Exceptional_Case
               | VC_Program_Exit_Post
               | VC_Exit_Case
               | VC_Inline_Check
               | VC_Container_Aggr_Check
               | VC_Reclamation_Check
               | VC_Feasible_Post
            =>
               return Functional_Contracts;

            when VC_Weaker_Pre
               | VC_Trivial_Weaker_Pre
               | VC_Stronger_Post
               | VC_Weaker_Classwide_Pre
               | VC_Stronger_Classwide_Post
               | VC_Weaker_Pre_Access
               | VC_Stronger_Post_Access
            =>
               return LSP;

            when VC_Warning_Kind
            =>
               return Warnings;
         end case;
      end VC_Kind_To_Summary;

   begin
      --  Build the list of .spark files that actually exist, parsing each one.
      --  ??? For now we silently skip missing .spark files; ideally the
      --  report should mention that some units were not analyzed.
      for Filename of SPARK_Files loop
         if Ada.Directories.Exists (Filename) then
            begin
               Parsed_Files.Append
                 (SPARK_File_Data'
                    (File => To_Unbounded_String (Filename),
                     Data => Read_File_Into_JSON (Filename)));
            exception
               when others =>
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "spark_report: error when processing file "
                     & Filename
                     & ", skipping");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "spark_report: try cleaning proofs to remove this error");
            end;
         end if;
      end loop;

      for File_Data of Parsed_Files loop
         begin
            Handle_SPARK_File (To_String (File_Data.File), File_Data.Data);
         exception
            when others =>
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  "spark_report: error when processing file "
                  & To_String (File_Data.File)
                  & ", skipping");
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  "spark_report: try cleaning proofs to remove this error");
         end;
      end loop;

      --  Build the command line string once for use in header and SARIF report
      declare
         use Ada.Command_Line;
      begin
         Append
           (Command_Line_Image,
            Ada.Directories.Base_Name
              (Ada.Directories.Simple_Name (Command_Name)));
         for J in 1 .. Argument_Count loop
            Append (Command_Line_Image, ' ');
            Append (Command_Line_Image, Argument (J));
         end loop;
      end;

      Ada.Text_IO.Create
        (Handle,
         Ada.Text_IO.Out_File,
         Ada.Directories.Compose (Out_Dir, "gnatprove.out"));

      if Assumptions then
         Compute_Assumptions;
      end if;

      if Output_Header then
         Show_Header (Handle, To_String (Command_Line_Image));
         Ada.Text_IO.New_Line (Handle);
         Ada.Text_IO.New_Line (Handle);
      end if;

      if SPARK_Mode_OK then
         if Max_Progress >= Progress_Flow then
            Dump_Summary_Table (Handle);
            Ada.Text_IO.New_Line (Handle);
            Ada.Text_IO.New_Line (Handle);
         end if;
         if Max_Progress >= Progress_Proof then
            Print_Max_Steps (Handle);
         end if;
      else

         --  If nothing has produced checks, we generate a warning with
         --  possible explanation, unless:
         --  the "quiet" switch was present
         --  or mode is "check" or "check all"
         --  or there were previous errors in gnatprove

         if not Quiet
           and then not Has_Errors
           and then Mode not in GPM_Check | GPM_Check_All
           and then not Has_Check
         then
            declare
               Err_Warn : constant String :=
                 (if Has_Limit_Switches then "error" else "warning");
            begin
               Error_Code := 1;
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  Err_Warn & ": no checks generated by GNATprove");
               if Has_Limit_Switches then
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "possible reason: wrong parameters to switches"
                     & " such as --limit-subp or --limit-line");
               else
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "possible reason: no bodies have been selected"
                     & " for analysis with SPARK_Mode");
                  Ada.Text_IO.Put_Line
                    (Ada.Text_IO.Standard_Error,
                     "possible fix: enable analysis of a non-generic"
                     & " body using SPARK_Mode");
               end if;
            end;
         end if;
      end if;

      --  Similarly, we print a success message if some checks exist and
      --  all have been proved. Suppressed if we are in mode "quiet".

      if not Quiet
        and then not Has_Errors
        and then Has_Check
        and then not Has_Unproved_Check
      then
         declare
            Sum          : Summary_Line renames Summary (Total);
            Total_VCs    : constant Natural :=
              Sum.Flow + Sum.Justified + Sum.Provers.Total + Sum.Unproved;
            Enable_Green : constant String :=
              (if Colors then ASCII.ESC & "[32m" & ASCII.ESC & "[K" else "");
            Reset_Color  : constant String :=
              (if Colors then ASCII.ESC & "[m" & ASCII.ESC & "[K" else "");
            Checks       : constant String :=
              (if Total_VCs = 1 then "check" else "checks");
            Total        : constant String := Natural'Image (Total_VCs);
         begin
            Ada.Text_IO.Put_Line
              (Enable_Green
               & "Success:"
               & Reset_Color
               & " all checks proved ("
               & Total (Total'First + 1 .. Total'Last)
               & " "
               & Checks
               & ").");
         end;
      end if;

      Print_Most_Difficult_Proved_Checks (Handle);
      Print_Analysis_Report (Handle);
      Ada.Text_IO.Close (Handle);

      --  Communicate to gnatprove that there were some unproved checks
      if Has_Unproved_Check then
         Error_Code := Unproved_Checks_Error_Status;
      end if;

      Generate_SARIF_Report
        (Filename           =>
           Ada.Directories.Compose (Out_Dir, "gnatprove.sarif"),
         SPARK_Files        => Parsed_Files,
         Command_Line_Image => To_String (Command_Line_Image),
         Error_Code         => Error_Code,
         Tree               => Tree);

      Status := Error_Code;
   end Generate_Report;

   procedure Generate_SARIF_Report
     (Filename           : String;
      SPARK_Files        : SPARK_File_Lists.List;
      Command_Line_Image : String;
      Error_Code         : Integer;
      Tree               : GPR2.Project.Tree.Object)
   is separate;

end Spark_Report;
