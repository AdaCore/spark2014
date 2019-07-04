------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           S P A R K _ R E P O R T                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2018, AdaCore                   --
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
--  For each unit, the tool expects a file "<unit>.spark" be be present. This
--  file is in JSON format. The format of these files is documented in the
--  user's guide.

with Ada.Calendar;
with Ada.Containers;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Strings.Unbounded;
with Ada.Text_IO;
with Assumptions;                         use Assumptions;
with Assumptions.Search;                  use Assumptions.Search;
with Assumption_Types;                    use Assumption_Types;
with Call;                                use Call;
with Configuration;
with GNAT.Calendar.Time_IO;
with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;                         use GNAT.OS_Lib;
with GNATCOLL.JSON;                       use GNATCOLL.JSON;
with GNATCOLL.Utils;                      use GNATCOLL.Utils;
with Platform;                            use Platform;
with Print_Table;                         use Print_Table;
with Report_Database;                     use Report_Database;
with SPARK2014VSN;                        use SPARK2014VSN;
with System;
with System.Storage_Elements;
with VC_Kinds;                            use VC_Kinds;

procedure SPARK_Report is

   No_Analysis_Done : Boolean := True;
   Assumptions      : Boolean := False;
   Output_Header    : Boolean := False;

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
   --  @param S a Flow kind like VC_DIVISION_CHECK etc
   --  @return the corresponding summary entry which this VC corresponds to

   function To_String (S : Summary_Entries) return String;
   --  compute the string which will appear in the leftmost column of the
   --  summary table for each check kind
   --  @param S the table line
   --  @return a string to be presented to the user

   procedure Process_Stats (C : Summary_Entries; Stats : JSON_Value);
   --  process the stats record for the VC and update the proof information
   --  @param C the category of the VC
   --  @param Stats the stats record

   procedure Show_Header (Handle : Ada.Text_IO.File_Type);
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

      T : Table := Create_Table (Lines => 10, Cols => 8);

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
         for Entr in Summary_Entries range Data_Dep .. LSP loop
            Tot.Flow := Tot.Flow + Summary (Entr).Flow;
            Tot.Interval :=
              Tot.Interval + Summary (Entr).Interval;
            Tot.CodePeer :=
              Tot.CodePeer + Summary (Entr).CodePeer;
            Tot.Provers.Total :=
              Tot.Provers.Total + Summary (Entr).Provers.Total;
            Tot.Justified := Tot.Justified + Summary (Entr).Justified;
            Tot.Unproved := Tot.Unproved + Summary (Entr).Unproved;
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
         Put_Cell (T, "Interval");
         Put_Cell (T, "CodePeer");
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
           Elt.Flow + Elt.Interval + Elt.CodePeer + Elt.Provers.Total +
             Elt.Justified + Elt.Unproved;
      begin
         Put_Cell (T, To_String (Line), Align => Left_Align);
         Put_Cell (T, Total);
         Put_Cell (T, Elt.Flow);
         Put_Cell (T, Elt.Interval);
         Put_Cell (T, Elt.CodePeer);
         Put_Provers_Cell (Elt.Provers);
         Put_Cell (T, Elt.Justified);
         Put_Cell (T, Elt.Unproved);
         New_Line (T);
      end Print_Table_Line;

      -----------------------
      -- Print_Table_Total --
      -----------------------

      procedure Print_Table_Total
      is
         Elt : Summary_Line renames Summary (Total);
         Tot : constant Natural :=
           Elt.Flow + Elt.Interval + Elt.CodePeer + Elt.Provers.Total +
             Elt.Justified + Elt.Unproved;
      begin
         Put_Cell (T, To_String (Total), Align => Left_Align);
         Put_Cell (T, Tot);
         Put_Total_Cell (Elt.Flow, Tot);
         Put_Total_Cell (Elt.Interval, Tot);
         Put_Total_Cell (Elt.CodePeer, Tot);
         Put_Total_Cell (Elt.Provers.Total, Tot);
         Put_Total_Cell (Elt.Justified, Tot);
         Put_Total_Cell (Elt.Unproved, Tot);
         New_Line (T);
      end Print_Table_Total;

      ----------------------
      -- Put_Provers_Cell --
      ----------------------

      procedure Put_Provers_Cell (Stats : in out All_Prover_Stat) is
         use Ada.Strings.Unbounded;
         use Prover_Stat_Maps;
         use Ada.Containers;
         Check_Total : constant Natural := Stats.Total;
         VC_Total    : Natural := 0;
         Buf         : Unbounded_String;
         First       : Boolean := True;
      begin
         if Check_Total = 0 or else Stats.Provers.Length = 0 then
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

         when Global_Missing
            | Global_Wrong
            | Export_Depends_On_Proof_In
            | Hidden_Unexposed_State
            | Illegal_Update
            | Non_Volatile_Function_With_Volatile_Effects
            | Volatile_Function_Without_Volatile_Effects
            | Side_Effects
            | Refined_State_Wrong
         =>
            return Data_Dep;

         when Impossible_To_Initialize_State
            | Initializes_Wrong
            | Uninitialized
            | Default_Initialization_Mismatch
         =>
            return Init;

         when Depends_Null
            | Depends_Missing
            | Depends_Missing_Clause
            | Depends_Wrong
         =>
            return Flow_Dep;

         when Dead_Code
            | Ineffective
            | Inout_Only_Read
            | Missing_Return
            | Not_Constant_After_Elaboration
            | Pragma_Elaborate_All_Needed
            | Pragma_Elaborate_Body_Needed
            | Reference_To_Non_CAE_Variable
            | Stable
            | Unused
            | Unused_Initial_Value
         =>
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
            Result : constant JSON_Value := Get (V, Index);
            Severe : constant String     := Get (Get (Result, "severity"));
            Subp   : constant Subp_Type  := From_JSON (Get (Result, "entity"));
            Kind   : constant Flow_Tag_Kind :=
              Flow_Tag_Kind'Value (Get (Get (Result, "rule")));
            Category : constant Possible_Entries :=
              Flow_Kind_To_Summary (Kind);
         begin
            if Has_Field (Result, "suppressed") then
               Add_Suppressed_Warning
                 (Unit   => Unit,
                  Subp   => Subp,
                  Reason => Get (Get (Result, "suppressed")),
                  File   => Get (Get (Result, "file")),
                  Line   => Get (Get (Result, "line")),
                  Column => Get (Get (Result, "col")));
               if Category /= No_Entry then
                  Increment (Summary (Category).Justified);
               end if;
            elsif Severe = "info" then
               --  Ignore flow info messages for now.
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

   ------------------------
   -- Handle_Proof_Items --
   ------------------------

   procedure Handle_Proof_Items (V : JSON_Array; Unit : Unit_Type) is
   begin
      for Index in 1 .. Length (V) loop
         declare
            Result   : constant JSON_Value := Get (V, Index);
            Severe   : constant String     := Get (Get (Result, "severity"));
            Kind     : constant VC_Kind    :=
              VC_Kind'Value (Get (Get (Result, "rule")));
            Subp     : constant Subp_Type :=
              From_JSON (Get (Result, "entity"));
            Category : constant Possible_Entries :=
              VC_Kind_To_Summary (Kind);
            Proved   : constant Boolean := Severe = "info";
         begin
            if Category = Warnings then
               null;

            elsif Has_Field (Result, "suppressed") then
               Increment (Summary (Category).Justified);
               Add_Suppressed_Warning
                 (Unit   => Unit,
                  Subp   => Subp,
                  Reason => Get (Get (Result, "suppressed")),
                  File   => Get (Get (Result, "file")),
                  Line   => Get (Get (Result, "line")),
                  Column => Get (Get (Result, "col")));

            else
               Add_Proof_Result
                 (Unit   => Unit,
                  Subp   => Subp,
                  Proved => Proved);
               if Proved then
                  declare
                     Cat : constant Prover_Category :=
                       From_JSON (Get (Result, "how_proved"));
                  begin
                     case Cat is
                        when PC_Interval =>
                           Increment (Summary (Category).Interval);
                        when PC_Codepeer =>
                           Increment (Summary (Category).CodePeer);
                        when PC_Prover =>
                           if Has_Field (Result, "stats") then
                              Process_Stats (Category, Get (Result, "stats"));
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
        (Item  : String;
         Index : Positive;
         Quit  : in out Boolean);
      --  Wrapper for Handle_SPARK_File

      -----------------------------
      -- Local_Handle_SPARK_File --
      -----------------------------

      procedure Local_Handle_SPARK_File
        (Item  : String;
         Index : Positive;
         Quit  : in out Boolean)
      is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_SPARK_File (Item);
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
      Dict      : constant JSON_Value :=
        Read (Read_File_Into_String (Fn), Fn);
      Basename  : constant String := Ada.Directories.Base_Name (Fn);
      Unit      : constant Unit_Type := Mk_Unit (Basename);
      Has_Flow  : constant Boolean := Has_Field (Dict, "flow");
      Has_Proof : constant Boolean := Has_Field (Dict, "proof");

      --  Status of analysis performed on all subprograms and packages of a
      --  unit depend on presence of the "flow" and "proof" files present in
      --  the .spark result file.

      --  This status is only relevant for subprograms and packages which are
      --  in SPARK. Also, we do not currently take into account the fact that
      --  possibly a single subprogram/line in the unit was analyzed.

      Analysis : constant Analysis_Status :=
        (if Has_Flow and Has_Proof then Flow_And_Proof
         elsif Has_Flow then Flow_Analysis
         elsif Has_Proof then Proof_Only
         else No_Analysis);

      Entries : constant JSON_Array := Get (Get (Dict, "spark"));
   begin
      for Index in 1 .. Length (Entries) loop
         declare
            Result   : constant JSON_Value := Get (Entries, Index);
            In_SPARK : constant Boolean :=
              Get (Get (Result, "spark")) = "all";
         begin
            Add_SPARK_Status
              (Unit         => Unit,
               Subp         => From_JSON (Result),
               SPARK_Status => In_SPARK,
               Analysis     => Analysis);

            --  If at least one subprogram or package was analyzed (either
            --  flow analysis or proof), then record that the analysis was
            --  effective.

            if In_SPARK and Analysis /= No_Analysis then
               No_Analysis_Done := False;
            end if;
         end;
      end loop;
      if Has_Flow then
         Handle_Flow_Items (Get (Get (Dict, "flow")), Unit);
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

      Source_Dirs : access String := null;
   begin
      for Index in 1 .. Argument_Count loop
         declare
            S : String renames Argument (Index);
         begin
            if S = "--assumptions" then
               Assumptions := True;
            elsif S = "--output-header" then
               Output_Header := True;
            elsif GNATCOLL.Utils.Starts_With (S, "--limit-subp=") then

               --  ??? FIXME --limit-subp currently ignored

               null;
            elsif GNATCOLL.Utils.Starts_With (S, "--") then
               Abort_With_Message ("unknown option: " & S);
            elsif Source_Dirs = null then
               Source_Dirs := new String'(S);
            else
               Abort_With_Message ("more than one file given, aborting");
            end if;
         end;
      end loop;
      if Source_Dirs = null then
         Abort_With_Message ("No source directory file given, aborting");
      end if;
      return Source_Dirs.all;
   end Parse_Command_Line;

   ---------------------------
   -- Print_Analysis_Report --
   ---------------------------

   procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type) is
      use Ada.Text_IO;

      procedure For_Each_Unit (Unit : Unit_Type);
      --  print proof results for the given unit

      -------------------
      -- For_Each_Unit --
      -------------------

      procedure For_Each_Unit (Unit : Unit_Type) is

         procedure For_Each_Subp (Subp : Subp_Type; Stat : Stat_Rec);

         -------------------
         -- For_Each_Subp --
         -------------------

         procedure For_Each_Subp (Subp : Subp_Type; Stat : Stat_Rec) is
         begin
            Put (Handle,
                 "  " & Subp_Name (Subp) & " at " &
                   To_String (Subp_Sloc (Subp)));

            if Stat.SPARK then
               if Stat.Analysis = No_Analysis then
                  Put_Line (Handle, " not analyzed");
               else
                  if Stat.Analysis in Flow_Analysis | Flow_And_Proof then
                     Put (Handle,
                          " flow analyzed ("
                          & Image (Stat.Flow_Errors, 1) & " errors, "
                          & Image (Stat.Flow_Checks, 1) & " checks and "
                          & Image (Stat.Flow_Warnings, 1) & " warnings)");
                  end if;

                  if Stat.Analysis = Flow_And_Proof then
                     Put (Handle, " and");
                  end if;

                  if Stat.Analysis in Proof_Only | Flow_And_Proof then
                     if Stat.Proof_Checks = Stat.Proof_Checks_OK then
                        Put (Handle,
                             " proved ("
                             & Image (Stat.Proof_Checks, 1) & " checks)");
                     else
                        Put (Handle,
                             " not proved," & Stat.Proof_Checks_OK'Img
                             & " checks out of" & Stat.Proof_Checks'Img
                             & " proved");
                     end if;
                  end if;

                  Put_Line (Handle, "");

                  if not Stat.Suppr_Msgs.Is_Empty then
                     Put_Line (Handle, "   suppressed messages:");
                     for Msg of Stat.Suppr_Msgs loop
                        Put_Line (Handle,
                                  "    " &
                                  Ada.Strings.Unbounded.To_String (Msg.File) &
                                    ":" & Image (Msg.Line, 1) & ":" &
                                    Image (Msg.Column, 1) & ": " &
                                    Ada.Strings.Unbounded.To_String
                                    (Msg.Reason));
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
               Put_Line (Handle, " skipped");
            end if;
         end For_Each_Subp;

      --  Start of processing for For_Each_Unit

      begin
         Put_Line (Handle,
                   "in unit " & Unit_Name (Unit) & ", "
                   & Image (Num_Subps_SPARK (Unit), 1)
                   & " subprograms and packages out of "
                   & Image (Num_Subps (Unit), 1) & " analyzed");
         Iter_Unit_Subps (Unit, For_Each_Subp'Access, Ordered => True);

      end For_Each_Unit;

      N_Un : constant Natural := Num_Units;

      Unit_Str : constant String :=
        (if N_Un = 1 then "unit" else "units");

   --  Start of processing for Print_Analysis_Report

   begin
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
      Ada.Text_IO.Put_Line (Handle,
                            "max steps used for successful proof:" &
                              Natural'Image (Max));
      Ada.Text_IO.New_Line (Handle);
   end Print_Max_Steps;

   -------------------
   -- Process_Stats --
   -------------------

   procedure Process_Stats (C : Summary_Entries; Stats : JSON_Value) is
      Map : constant Prover_Stat_Maps.Map := From_JSON (Stats);

   begin
      Merge_Stat_Maps (Summary (C).Provers.Provers, Map);
   end Process_Stats;

   -----------------
   -- Show_Header --
   -----------------

   procedure Show_Header (Handle : Ada.Text_IO.File_Type) is
      use Ada, Ada.Text_IO;

      function Get_Env_Variable (Name : String) return String;
      --  Return the value of environment variable Name

      function OS_String return String;
      --  Return a nice string for the OS GNATprove was compiled for

      ----------------------
      -- Get_Env_Variable --
      ----------------------

      function Get_Env_Variable (Name : String) return String is
         --  Return the value of the "Name" environment variable.
         Result : GNAT.OS_Lib.String_Access := GNAT.OS_Lib.Getenv (Name);
         Str    : constant String := Result.all;
      begin
         GNAT.OS_Lib.Free (Result);
         return Str;
      end Get_Env_Variable;

      ---------------
      -- OS_String --
      ---------------

      function OS_String return String is
         (case Get_OS_Flavor is
             when X86_Windows | X86_64_Windows => "Windows",
             when X86_Linux   | X86_64_Linux   => "Linux",
             when X86_64_Darwin                => "Darwin",
             when X86_64_FreeBSD               => "FreeBSD",
             when CodePeer_OS                  => "CodePeer OS");

      Pointer_Size : constant :=
        System.Storage_Elements.Integer_Address'Size / System.Storage_Unit;

   --  Start of processing for Show_Header

   begin
      Put_Line
        (Handle,
         "date               : " &
         GNAT.Calendar.Time_IO.Image (Date    => Ada.Calendar.Clock,
                                      Picture => "%Y-%m-%d %H:%M:%S"));
      Put_Line
        (Handle,
         "gnatprove version  : " & SPARK2014_Version_String);
      Put_Line
        (Handle,
         "host               : " & OS_String &
           Integer'Image (Pointer_Size * 8) & " bits");

      declare
         Cmd : constant String :=
           Get_Env_Variable ("GNATPROVE_CMD_LINE");
         GNATprove_Switches : constant String :=
           Get_Env_Variable ("GNATPROVE_SWITCHES");
      begin
         if Cmd /= "" then
            Put_Line
              (Handle, "command line       : " & Cmd);
            Put_Line
              (Handle, "gnatprove switches : " & GNATprove_Switches);
         end if;
      end;
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
            | VC_Length_Check
            | VC_Discriminant_Check
            | VC_Tag_Check
            | VC_Ceiling_Interrupt
            | VC_Interrupt_Reserved
            | VC_Ceiling_Priority_Protocol
            | VC_Task_Termination
            | VC_Raise
         =>
            return Runtime_Checks;

         when VC_Assert
            | VC_Loop_Invariant
            | VC_Loop_Invariant_Init
            | VC_Loop_Invariant_Preserv
            | VC_Loop_Variant
         =>
            return Assertions;

         when VC_Initial_Condition
            | VC_Default_Initial_Condition
            | VC_Precondition
            | VC_Precondition_Main
            | VC_Postcondition
            | VC_Refined_Post
            | VC_Contract_Case
            | VC_Disjoint_Contract_Cases
            | VC_Complete_Contract_Cases
            | VC_Inline_Check
         =>
            return Functional_Contracts;

         when VC_Weaker_Pre
            | VC_Trivial_Weaker_Pre
            | VC_Stronger_Post
            | VC_Weaker_Classwide_Pre
            | VC_Stronger_Classwide_Post
         =>
            return LSP;

         when VC_Warning_Kind
         =>
            return Warnings;
      end case;
   end VC_Kind_To_Summary;

   ---------------
   -- To_String --
   ---------------

   function To_String (Sloc : My_Sloc) return String is
      use Ada.Strings.Unbounded;

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
         Append (UB, ":");
         Append (UB, Image (S.Line, 1));
      end loop;
      return To_String (UB);
   end To_String;

   function To_String (S : Summary_Entries) return String is
   begin
      case S is
         when Data_Dep             => return "Data Dependencies";
         when Flow_Dep             => return "Flow Dependencies";
         when Init                 => return "Initialization";
         when Non_Aliasing         => return "Non-Aliasing";
         when Runtime_Checks       => return "Run-time Checks";
         when Assertions           => return "Assertions";
         when Functional_Contracts => return "Functional Contracts";
         when LSP                  => return "LSP Verification";
         when Total                => return "Total";
      end case;
   end To_String;

   procedure Iterate_Source_Dirs is new For_Line_In_File (Handle_Source_Dir);

   Source_Directories_File : constant String := Parse_Command_Line;

   use Ada.Text_IO;

   Handle : File_Type;

--  Start of processing for SPARK_Report

begin
   Iterate_Source_Dirs (Source_Directories_File);
   if No_Analysis_Done then
      Reset_All_Results;
   end if;

   Create (Handle,
           Out_File,
           Configuration.SPARK_Report_File
             (GNAT.Directory_Operations.Dir_Name (Source_Directories_File)));
   if Assumptions then
      Compute_Assumptions;
   end if;

   if Output_Header then
      Show_Header (Handle);
      Ada.Text_IO.New_Line (Handle);
      Ada.Text_IO.New_Line (Handle);
   end if;

   if not No_Analysis_Done then
      Dump_Summary_Table (Handle);
      Ada.Text_IO.New_Line (Handle);
      Ada.Text_IO.New_Line (Handle);
   end if;
   if not No_Analysis_Done then
      Print_Max_Steps (Handle);
   end if;
   Print_Analysis_Report (Handle);
   Close (Handle);

   --  Communicate to gnatprove that there were some unproved checks

   if Has_Unproved_Check then
      GNAT.OS_Lib.OS_Exit (Unproved_Checks_Error_Status);
   end if;
end SPARK_Report;
