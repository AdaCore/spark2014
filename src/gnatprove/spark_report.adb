------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           S P A R K _ R E P O R T                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

--  This program (SPARK_Report) is run at the very end of SPARK analysis (see
--  also the comment in gnatprove.adb). The different bits of analysis have
--  stored the results of the analysis in one result file per unit. This
--  program reads all those files in and prints a summary in a file called
--  "gnatprove.out".
--
--  For each unit, the tool expects a file "<unit>.spark" be present. This file
--  is in JSON format. The format of these files is documented in the
--  user's guide.

--  This program reads its configuration via a JSON file on the command line.
--  The format of this JSON file is as follows:

--  configuration_file = {
--     "obj_dirs" : list string,
--     "cmd_line" : list string,
--     "switches" : list string,
--     "proof_switches" : proof_switches_entry,
--     "assumptions" : bool,
--     "has_errors" : bool,
--     "has_limit_switches" : bool,
--     "mode" : string,
--     "output_header" : bool,
--     "quiet" : bool,
--     "colors" : bool,
--  }
--  Note that all fields are optional and absence of a value indicates default
--  values for the corresponding fields: the empty list for lists, "false" for
--  booleans. For the field "limit_subp", absence of the field means no such
--  limit was requested.

--  proof_switches_entry = {
--    key : list string
--  }

--  The meaning of the various fields is as follows:
--  obj_dirs: list of directories to scan for .spark files
--  cmd_line: the commandline of gnatprove to record in the gnatprove.out file
--  switches: the list of switches provided via the Switches attribute
--  proof_switches: a mapping of keys to lists of strings, as provided via the
--     Proof_Switches attribute
--  assumptions: if true, spark_report should generate assumption information
--  output_header: if true, spark_report should generate a header which
--    contains information such as switches, gnatprove version, and more.
--  has_errors: previous phases of gnatprove contain error messages
--  has_limit_switches: true if any --limit-* switches have been passed
--  mode: the maximal mode of analysis (stone, bronze, etc) used for this
--  gnatprove run

with Ada.Calendar;
with Ada.Containers;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;
with Assumptions;           use Assumptions;
with Assumptions.Search;    use Assumptions.Search;
with Assumption_Types;      use Assumption_Types;
with Call;                  use Call;
with GNAT.Calendar.Time_IO;
with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with Platform;              use Platform;
with Print_Table;           use Print_Table;
with Report_Database;       use Report_Database;
with SPARK2014VSN;          use SPARK2014VSN;
with System;
with System.Storage_Elements;
with VC_Kinds;              use VC_Kinds;

procedure SPARK_Report is

   SPARK_Mode_OK : Boolean := False;
   --  This variable is set to True when at least one subprogram was analyzed
   --  as being in SPARK.

   Max_Progress       : Analysis_Progress := Progress_None;
   Assumptions        : Boolean := False;
   Output_Header      : Boolean := False;
   Quiet              : Boolean := False;
   Has_Limit_Switches : Boolean := False;
   Has_Errors         : Boolean := False;
   Colors             : Boolean := False;

   Mode : GP_Mode;

   Error_Code : Integer := 0;

   End_Time : constant String :=
     GNAT.Calendar.Time_IO.Image
       (Date      => Ada.Calendar.Clock,
        Picture   => "%Y-%m-%dT%H:%M:%SZ",
        Time_Zone => 0);
   --  End time of analysis, used for the reports. Time zone "0" is UTC.

   function Parse_Command_Line return String;
   --  Parse the command line and set the variables Assumptions and Limit_Subp.
   --  Return the name of the file which contains the object dirs to be
   --  scanned.

   procedure Handle_SPARK_File (Fn : String);
   --  Parse and extract all information from a single SPARK file.
   --  No_Analysis_Done is left as true if no subprogram or package was
   --  analyzed in this unit.

   procedure Handle_Flow_Items (V : JSON_Array; Unit : Unit_Type);
   --  Parse and extract all information from a flow result array

   procedure Handle_Pragma_Assume_Items (V : JSON_Array; Unit : Unit_Type);
   --  Parse and extract all information from a pragma assume result array

   procedure Handle_Proof_Items (V : JSON_Array; Unit : Unit_Type);
   --  Parse and extract all information from a proof result array

   procedure Handle_Assume_Items (V : JSON_Array; Unit : Unit_Type);
   --  Parse and extract all information from a proof result array

   procedure Handle_Source_Dir (Dir : String);
   --  Parse all result files in the given directory

   procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type);
   --  Print the proof report in the given file

   procedure Print_Max_Steps (Handle : Ada.Text_IO.File_Type);
   --  Print a line that summarizes the maximum required steps

   procedure Print_Most_Difficult_Proved_Checks
     (Handle : Ada.Text_IO.File_Type);
   --  Print the set of most difficult checks to prove

   procedure Compute_Assumptions;
   --  Compute remaining assumptions for all subprograms and store them in
   --  database.

   function To_String (Sloc : My_Sloc) return String;
   --  Pretty-printing of slocs including instantiation chains

   procedure Dump_Summary_Table (Handle : Ada.Text_IO.File_Type);
   --  Print the summary table to a file
   --  @param Handle the file handle to print the summary table to

   procedure Increment (X : in out Integer);
   --  @param X increment its parameter by 1

   function VC_Kind_To_Summary (S : VC_Kind) return Possible_Entries;
   --  @param S a VC kind like VC_DIVISION_CHECK etc
   --  @return the corresponding summary entry which this VC corresponds to

   function Flow_Kind_To_Summary (S : Flow_Tag_Kind) return Possible_Entries;
   --  @param S a Flow kind like ALIASING etc
   --  @return the corresponding summary entry which this VC corresponds to

   function To_String (S : Summary_Entries) return String;
   --  compute the string which will appear in the leftmost column of the
   --  summary table for each check kind
   --  @param S the table line
   --  @return a string to be presented to the user

   function Build_Switches_String (A : JSON_Array) return String;
   --  @param a JSON array of strings
   --  @return a string that concatenates all strings in the array, with spaces
   --    as separators.

   procedure Process_Stats
     (C         : Summary_Entries;
      Stats     : Prover_Stat_Maps.Map;
      Max_Steps : out Natural;
      Max_Time  : out Float);
   --  process the stats record for the VC and update the proof information
   --  @param C the category of the VC
   --  @param Stats the stats record
   --  @param Max_Steps maximum value of steps in Stats
   --  @param Max_Time maximum value of time in Stats

   procedure Show_Header (Handle : Ada.Text_IO.File_Type; Info : JSON_Value);
   --  Print header at start of generated file "gnatprove.out"

   procedure Generate_SARIF_Report (Filename : String; Info : JSON_Value);
   --  Generate SARIF report in "gnatprove.sarif"

   ---------------------------
   -- Build_Switches_String --
   ---------------------------

   function Build_Switches_String (A : JSON_Array) return String is
      Buffer : Unbounded_String;
      First  : Boolean := True;
   begin
      for I in Positive range 1 .. Length (A) loop
         if not First then
            Append (Buffer, ' ');
         else
            First := False;
         end if;
         Append (Buffer, String'(Get (Get (A, I))));
      end loop;
      return To_String (Buffer);
   end Build_Switches_String;

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
      --  print the header of the table

      procedure Print_Table_Line (Line : Summary_Entries);
      --  print a line of the table other than the header and the total line
      --  @param Line the entry of the summary to be printed

      procedure Print_Table_Total;
      --  print the "Total" line of the table

      procedure Put_Provers_Cell (Stats : in out All_Prover_Stat);
      --  print the "provers" cell of a category, with the total count of
      --  checks and the percentage of each prover
      --  @param Stats the stats for the prover

      procedure Put_Total_Cell (Part, Total : Natural);
      --  print a number cell, and if not zero, print the percentage this
      --  represents in some total, in the way "32 (14%)"
      --  @param Part the number to be shown in this cell
      --  @param Total the total (ie. 100%)

      procedure Compute_Total_Summary_Line;
      --  compute the numbers for the "Total" line of the summary table

      function Integer_Percent (Part, Total : Integer) return Integer
      with Post => Integer_Percent'Result in 0 .. 100;
      --  compute the percentage of Part in Total, using Integers
      --  @param Part the part
      --  @param Total the total count
      --  @return an integer close to the percentage that Part represents of
      --  Total

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
         --  The very first cell is the upper left corner of the table, which
         --  is empty.

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

      --  Start of processing for Dump_Summary_Table

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

   function Flow_Kind_To_Summary (S : Flow_Tag_Kind) return Possible_Entries is
   begin
      case S is
         when Empty_Tag =>
            return No_Entry;

         when Aliasing =>
            return Non_Aliasing;

         when Call_To_Current_Task =>
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
            | Unused_Global
            | Volatile_Function_Without_Volatile_Effects
         =>
            return Data_Dep;

         when Impossible_To_Initialize_State
            | Initializes_Wrong
            | Uninitialized
            | Default_Initialization_Mismatch
         =>
            return Init;

         when Depends_Missing
            | Depends_Missing_Clause
            | Depends_Null
            | Depends_Wrong
         =>
            return Flow_Dep;

         when Call_In_Type_Invariant | Subprogram_Termination =>
            return Termination;

         when Dead_Code
            | Ineffective
            | Inout_Only_Read
            | Missing_Return
            | Not_Constant_After_Elaboration
            | Reference_To_Non_CAE_Variable
            | Stable
            | Unused_Initial_Value
            | Unused_Variable
         =>
            return No_Entry;
      end case;
   end Flow_Kind_To_Summary;

   ---------------------------
   -- Generate_SARIF_Report --
   ---------------------------

   procedure Generate_SARIF_Report (Filename : String; Info : JSON_Value)
   is separate;

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

   procedure Handle_Pragma_Assume_Items (V : JSON_Array; Unit : Unit_Type) is
   begin
      for Index in 1 .. Length (V) loop
         declare
            Result : constant JSON_Value := Get (V, Index);
            File   : constant String := Get (Result, "file");
            Line   : constant Positive := Get (Result, "line");
            Column : constant Positive := Get (Result, "col");
            Subp   : constant Subp_Type := From_JSON (Get (Result, "entity"));
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
            Category : constant Possible_Entries := VC_Kind_To_Summary (Kind);
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
               Add_Proof_Result (Unit => Unit, Subp => Subp, Proved => Proved);
               if Proved then
                  declare
                     Cat : constant Prover_Category :=
                       From_JSON (Get (Result, "how_proved"));
                  begin
                     case Cat is
                        when PC_Trivial =>

                           --  For the "trivial" category (proof of some check
                           --  inside gnat2why), we insert a proof by the
                           --  "Trivial" prover that took one step and 0.0
                           --  time.

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

                        when PC_Prover =>
                           if Has_Field (Result, "stats") then
                              declare
                                 Stats     : constant Prover_Stat_Maps.Map :=
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
                                       File      => To_Unbounded_String (File),
                                       Line      => Line,
                                       Column    => Column,
                                       Max_Steps => Max_Steps,
                                       Max_Time  => Max_Time));
                              end;
                           end if;
                           Increment (Summary (Category).Provers.Total);

                        when PC_Flow =>
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
   -- Handle_Source_Dir --
   -----------------------

   procedure Handle_Source_Dir (Dir : String) is

      procedure Local_Handle_SPARK_File
        (Item : String; Index : Positive; Quit : in out Boolean);
      --  Wrapper for Handle_SPARK_File

      -----------------------------
      -- Local_Handle_SPARK_File --
      -----------------------------

      procedure Local_Handle_SPARK_File
        (Item : String; Index : Positive; Quit : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_SPARK_File (Item);
      exception
         when E : others =>
            pragma
              Debug
                (Ada.Text_IO.Put_Line
                   (Ada.Text_IO.Standard_Error,
                    "spark_report: " & Ada.Exceptions.Exception_Message (E)));
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "spark_report: error when processing file "
               & Item
               & ", skipping");
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "spark_report: try cleaning proofs to remove this error");
      end Local_Handle_SPARK_File;

      procedure Iterate_SPARK is new
        GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_SPARK_File);

      Save_Dir : constant String := Ada.Directories.Current_Directory;

      --  Start of processing for Handle_Source_Dir

   begin
      Ada.Directories.Set_Directory (Dir);
      Iterate_SPARK (Path => "*." & VC_Kinds.SPARK_Suffix);
      Ada.Directories.Set_Directory (Save_Dir);
   exception
      when others =>
         Ada.Directories.Set_Directory (Save_Dir);
         raise;
   end Handle_Source_Dir;

   -----------------------
   -- Handle_SPARK_File --
   -----------------------

   procedure Handle_SPARK_File (Fn : String) is

      Basename : constant String := Ada.Directories.Base_Name (Fn);
      Unit     : constant Unit_Type := Mk_Unit (Basename);

      procedure Handle_SPARK_Status (Name : UTF8_String; Value : JSON_Value);
      --  Handle one entry of the "spark" status map

      -------------------------
      -- Handle_SPARK_Status --
      -------------------------

      procedure Handle_SPARK_Status (Name : UTF8_String; Value : JSON_Value) is
         SPARK_Status : constant SPARK_Mode_Status := From_JSON (Value);
      begin
         Add_SPARK_Status
           (Unit         => Unit,
            Subp         => From_Key (Name),
            SPARK_Status => SPARK_Status);

         --  If at least one subprogram or package is fully in SPARK, then
         --  record that SPARK_Mode is likely set at least somewhere.

         if SPARK_Status = All_In_SPARK then
            SPARK_Mode_OK := True;
         end if;

      end Handle_SPARK_Status;

      Dict        : constant JSON_Value := Read_File_Into_JSON (Fn);
      Has_Flow    : constant Boolean := Has_Field (Dict, "flow");
      Has_Assumes : constant Boolean := Has_Field (Dict, "pragma_assume");
      Has_Proof   : constant Boolean := Has_Field (Dict, "proof");

      --  Status of analysis performed on all subprograms and packages of a
      --  unit depend on presence of the "flow" and "proof" files present in
      --  the .spark result file.

      --  This status is only relevant for subprograms and packages which are
      --  in SPARK. Also, we do not currently take into account the fact that
      --  possibly a single subprogram/line in the unit was analyzed.

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
         Handle_Pragma_Assume_Items (Get (Get (Dict, "pragma_assume")), Unit);
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

   ------------------------
   -- Parse_Command_Line --
   ------------------------

   function Parse_Command_Line return String is
      use Ada.Command_Line;
   begin
      if Argument_Count > 1 then
         Abort_With_Message ("more than one file or option given, aborting");
      end if;
      if Argument_Count < 1 then
         Abort_With_Message ("No source directory file given, aborting");
      end if;
      return Argument (1);
   end Parse_Command_Line;

   ---------------------------
   -- Print_Analysis_Report --
   ---------------------------

   procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type) is
      use Ada.Text_IO;

      function To_String (Reason : Stop_Reason_Type) return String;
      --  Produce human readable string for the reason the analysis did not
      --  progress further.

      procedure For_Each_Unit (Unit : Unit_Type);
      --  print proof results for the given unit

      -------------------
      -- For_Each_Unit --
      -------------------

      procedure For_Each_Unit (Unit : Unit_Type) is

         procedure For_Each_Subp
           (Subp : Subp_Type; Stat : Stat_Rec; Analysis : Analysis_Progress);

         -------------------
         -- For_Each_Subp --
         -------------------

         procedure For_Each_Subp
           (Subp : Subp_Type; Stat : Stat_Rec; Analysis : Analysis_Progress) is

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
                     " not analyzed (pragma Annotate Skip_Flow_And_Proof)");
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
                           ", proof skipped (pragma Annotate Skip_Proof)");
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
                           --  justification kind and reason, e.g.
                           --  "(marked as: intentional, with reason: not
                           --  possible)".

                        begin
                           Put_Line
                             (Handle,
                              "    "
                              --  file, line, column, e.g. "p.adb:42:6:"
                              & To_String (Msg.File)
                              & ":"
                              & Image (Msg.Line, 1)
                              & ":"
                              & Image (Msg.Column, 1)
                              & ":"

                              --  justification message, e.g. "overflow
                              --  check failed"
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
                              To_String (Rule.Claim) & " fully established");
                        else
                           Ada.Text_IO.Put_Line
                             (Handle, To_String (Rule.Claim) & " depends on");
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

         --  Start of processing for For_Each_Unit

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
            when Stop_Reason_None =>
               return "";

            when Stop_Reason_Generic_Unit =>
               return "generic unit is not analyzed";

            when Stop_Reason_Check_Mode =>
               return "only SPARK_Mode checking was requested";

            when Stop_Reason_Flow_Mode =>
               return "only flow analysis was requested";

            when Stop_Reason_Error_Marking =>
               return "error during checking of SPARK_Mode";

            when Stop_Reason_Error_Flow =>
               return "error during flow analysis";

            when Stop_Reason_Error_Borrow =>
               return "error during ownership checking";
         end case;
      end To_String;

      N_Un : constant Natural := Num_Units;

      Unit_Str : constant String := (if N_Un = 1 then "unit" else "units");

      --  Start of processing for Print_Analysis_Report

   begin
      Ada.Text_IO.Put_Line (Handle, "========================");
      Ada.Text_IO.Put_Line (Handle, "Detailed analysis report");
      Ada.Text_IO.Put_Line (Handle, "========================");
      Ada.Text_IO.New_Line (Handle);

      if N_Un > 0 then
         Put_Line (Handle, "Analyzed" & N_Un'Img & " " & Unit_Str);
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
        (Handle, "max steps used for successful proof:" & Natural'Image (Max));
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
                  & f"{Kind_Name (PC.Kind)} proved in max {Max_Time} seconds");
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

   procedure Show_Header (Handle : Ada.Text_IO.File_Type; Info : JSON_Value) is
      use Ada, Ada.Text_IO;

      function OS_String return String;
      --  Return a nice string for the OS GNATprove was compiled for

      procedure Print_Switch_Entry (Name : UTF8_String; Value : JSON_Value);
      --  Print one entry of the Proof_Switches attribute

      ------------------------
      -- Print_Switch_Entry --
      ------------------------

      procedure Print_Switch_Entry (Name : UTF8_String; Value : JSON_Value) is
      begin
         Put_Line
           (Handle, "   " & Name & ": " & Build_Switches_String (Get (Value)));
      end Print_Switch_Entry;

      ---------------
      -- OS_String --
      ---------------

      function OS_String return String
      is (case Get_OS_Flavor is
            when X86_Windows | X86_64_Windows => "Windows",
            when X86_Linux | X86_64_Linux | AArch64_Linux => "Linux",
            when X86_64_Darwin => "Darwin",
            when X86_64_FreeBSD => "FreeBSD",
            when GNATSAS_OS => "GNATSAS OS",
            when AArch64_Darwin => "Darwin");

      Pointer_Size : constant :=
        System.Storage_Elements.Integer_Address'Size / System.Storage_Unit;

      --  Start of processing for Show_Header

   begin
      Put_Line (Handle, "date               : " & End_Time);
      Put_Line (Handle, "gnatprove version  : " & SPARK2014_Version_String);
      Put_Line
        (Handle,
         "host               : "
         & OS_String
         & Integer'Image (Pointer_Size * 8)
         & " bits");

      if Has_Field (Info, "cmdline") then
         Put_Line
           (Handle,
            "command line       : "
            & Build_Switches_String (Get (Info, "cmdline")));
      end if;
      if Has_Field (Info, "switches") then
         Put_Line
           (Handle,
            "Switches attribute: "
            & Build_Switches_String (Get (Info, "switches")));
      end if;
      if Has_Field (Info, "proof_switches") then
         Put_Line (Handle, " Proof_Switches attribute:");
         Map_JSON_Object
           (Get (Info, "proof_switches"), Print_Switch_Entry'Access);
      end if;
   end Show_Header;

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
            | VC_UC_Alignment
            | VC_Unchecked_Union_Restriction
            | VC_UC_Volatile
            | VC_Validity_Check
         =>
            return Runtime_Checks;

         when VC_Initialization_Check =>
            return Init;

         when VC_Assert
            | VC_Assert_Premise
            | VC_Assert_Step
            | VC_Loop_Invariant
            | VC_Loop_Invariant_Init
            | VC_Loop_Invariant_Preserv
         =>
            return Assertions;

         when VC_Loop_Variant | VC_Subprogram_Variant | VC_Termination_Check =>
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

         when VC_Warning_Kind =>
            return Warnings;
      end case;
   end VC_Kind_To_Summary;

   ---------------
   -- To_String --
   ---------------

   function To_String (Sloc : My_Sloc) return String is
      First : Boolean := True;
      UB    : Unbounded_String;

   begin
      for S of Sloc loop
         if not First then
            Append (UB, ", instantiated at ");
         else
            First := False;
         end if;
         Append (UB, Base_Sloc_File (S));
         Append (UB, ':');
         Append (UB, Image (S.Line, 1));
      end loop;
      return To_String (UB);
   end To_String;

   function To_String (S : Summary_Entries) return String is
   begin
      case S is
         when Data_Dep =>
            return "Data Dependencies";

         when Flow_Dep =>
            return "Flow Dependencies";

         when Init =>
            return "Initialization";

         when Non_Aliasing =>
            return "Non-Aliasing";

         when Runtime_Checks =>
            return "Run-time Checks";

         when Assertions =>
            return "Assertions";

         when Functional_Contracts =>
            return "Functional Contracts";

         when LSP =>
            return "LSP Verification";

         when Termination =>
            return "Termination";

         when Concurrency =>
            return "Concurrency";

         when Total =>
            return "Total";
      end case;
   end To_String;

   Source_Directories_File : constant String := Parse_Command_Line;

   use Ada.Text_IO;

   Handle : File_Type;

   Info : constant JSON_Value := Read_File_Into_JSON (Source_Directories_File);

   --  Start of processing for SPARK_Report

begin

   --  Processing of config options

   Assumptions :=
     Has_Field (Info, "assumptions") and then Get (Info, "assumptions") = True;
   Output_Header :=
     Has_Field (Info, "output_header")
     and then Get (Info, "output_header") = True;
   Quiet := Has_Field (Info, "quiet") and then Get (Info, "quiet") = True;

   Has_Limit_Switches :=
     Has_Field (Info, "has_limit_switches")
     and then Get (Info, "has_limit_switches") = True;

   Mode := From_JSON (Get (Info, "mode"));
   Has_Errors := Get (Info, "has_errors");
   Colors := Get (Info, "colors");

   if Has_Field (Info, "obj_dirs") then
      declare
         Ar : constant JSON_Array := Get (Info, "obj_dirs");
      begin
         for Var_Index in Positive range 1 .. Length (Ar) loop
            Handle_Source_Dir (Get (Get (Ar, Var_Index)));
         end loop;
      end;
   end if;

   Create
     (Handle,
      Out_File,
      Ada.Directories.Compose
        (GNAT.Directory_Operations.Dir_Name (Source_Directories_File),
         "gnatprove.out"));
   if Assumptions then
      Compute_Assumptions;
   end if;

   if Output_Header then
      Show_Header (Handle, Info);
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

      --  If nothing has produced checks, we generate a warning with possible
      --  explanation, unless:
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
            Put_Line
              (Standard_Error,
               Err_Warn & ": no checks generated by GNATprove");
            if Has_Limit_Switches then
               Put_Line
                 (Standard_Error,
                  "possible reason: wrong parameters to switches"
                  & " such as --limit-subp or --limit-line");
            else
               Put_Line
                 (Standard_Error,
                  "possible reason: no bodies have been selected"
                  & " for analysis with SPARK_Mode");
               Put_Line
                 (Standard_Error,
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
         Put_Line
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
   Close (Handle);

   --  Communicate to gnatprove that there were some unproved checks

   if Has_Unproved_Check then
      Error_Code := Unproved_Checks_Error_Status;
   end if;

   Generate_SARIF_Report
     (Ada.Directories.Compose
        (GNAT.Directory_Operations.Dir_Name (Source_Directories_File),
         "gnatprove.sarif"),
      Info);

   GNAT.OS_Lib.OS_Exit (Error_Code);
end SPARK_Report;
