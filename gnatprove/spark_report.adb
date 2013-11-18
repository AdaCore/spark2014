------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                           S P A R K _ R E P O R T                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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
--  stored the results of the analysis in various files, This program reads
--  all those files in and prints a summary in a file called "gnatprove.out".
--
--  For each unit, the tool expects files to be present that look like this:
--    * <unit>.spark contains the SPARK status for all subprograms and packages
--    * <unit>.flow contains the flow warnings/error messages for all
--         subprograms and packages in SPARK
--    * <unit>.proof contains the proved/unproved VCs for all subprograms and
--        packages in SPARK
--
--  All these files are JSON files, and contain a list of entries that will be
--  read in by SPARK_Report. We now describe the format of each file.
--
--  --------------
--  -- Entities --
--  --------------
--
--  At various places, we refer to entities. These are Ada entities,
--  subprograms or packages. Entities are defined by their name and their
--  source location (file and line). In JSON this translates to the following
--  dictionary for entities:
--    { name  : string,
--      file  : string,
--      line  : int }

--  -----------------------
--  -- SPARK status file --
--  -----------------------
--
--  This file is called <unit>.spark and is a list of entities, with an extra
--  field for spark status, so that the entire dict looks like this:
--    { name  : string,
--      file  : string,
--      line  : int,
--      spark : string }
--  the entry "spark" is one of "all", "spec" or "no" and describes the SPARK
--  status of the entity.
--
--  -----------------
--  --  Proof File --
--  -----------------
--
--  This file is called <unit>.proof and is a list of dictionaries of the
--  folling form:
--    { file     : string,
--      line     : int,
--      col      : int,
--      message  : string,
--      rule     : string,
--      severity : string,
--      tracefile: string,
--      entity   : entity }
--  - (file, line, col) describe the source location of the message.
--  - "message" is the message text.
--  - "rule" describes the kind of VC, the possible values are described
--    in the file vc_kinds.ads.
--  - "severity" describes the kind status of the message, possible values used
--    by gnatwhy3 are "info" and "error"
--  - "tracefile" contains the name of a trace file, if any
--  - "entity" contains the entity dictionary for the entity that this VC
--    belongs to
--
--  ----------------
--  --  Flow File --
--  ----------------
--
--  This file is called <unit>.flow and is a list of dictionaries of the same
--  form as for proof. Differences are in the possible values for:
--  - severity: ??? document what severities flow uses
--  - rule:     ??? document possible values for flow
--  The special value "pragma_warning" is used for suppressed warnings. In
--  this case, the field "message" contains the reason for the message to
--  be suppressed, instead of the message string.

with Ada.Command_Line;
with Ada.Directories;
with Ada.Strings.Unbounded;
with Ada.Text_IO;

with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;             use GNAT.OS_Lib;

with GNATCOLL.JSON;

with Call;                    use Call;
with String_Utils;            use String_Utils;
with VC_Kinds;

with Configuration;           use Configuration;
with Report_Database;         use Report_Database;

procedure SPARK_Report is

   procedure Handle_SPARK_File
     (Fn               : String;
      No_Analysis_Done : out Boolean);
   --  Parse and extract all information from a single SPARK file.
   --  No_Analysis_Done is set to true if no subprogram or package was
   --  analyzed in this unit.

   procedure Handle_Flow_File (Fn : String);
   --  Parse and extract all information from a flow result file

   procedure Handle_Proof_File (Fn : String);
   --  Parse and extract all information from a proof result file

   procedure Handle_Source_Dir (Dir : String);
   --  Parse all result files of this directory.

   function Mk_Subp_Of_Entity (Ent : GNATCOLL.JSON.JSON_Value)
      return Subp_Type;
   --  convert a json entity dict to a subp

   procedure Print_Analysis_Report (Handle : Ada.Text_IO.File_Type);
   --  print the proof report in the given file

   -----------------------
   -- Mk_Subp_Of_Entity --
   -----------------------

   function Mk_Subp_Of_Entity (Ent : GNATCOLL.JSON.JSON_Value)
                               return Subp_Type is
      use GNATCOLL.JSON;
   begin
      return
        Mk_Subp (Get (Get (Ent, "name")),
                 Get (Get (Ent, "file")),
                 Get (Get (Ent, "line")));
   end Mk_Subp_Of_Entity;

   ----------------------
   -- Handle_Flow_File --
   ----------------------

   procedure Handle_Flow_File (Fn : String) is
      use GNATCOLL.JSON;
      Dict : constant JSON_Value := Read (Read_File_Into_String (Fn), Fn);
      Unit : constant Unit_Type := Mk_Unit (Ada.Directories.Base_Name (Fn));
      Entries : constant JSON_Array := Get (Dict);
   begin
      for Index in 1 .. Length (Entries) loop
         declare
            Result : constant JSON_Value := Get (Entries, Index);
            Severe : constant String     := Get (Get (Result, "severity"));
            Kind   : constant String     := Get (Get (Result, "rule"));
            Subp   : constant Subp_Type  :=
              Mk_Subp_Of_Entity (Get (Result, "entity"));
         begin
            if Kind = "pragma_warning" then
               Add_Suppressed_Warning
                 (Unit   => Unit,
                  Subp   => Subp,
                  Reason => Get (Get (Result, "message")),
                  File   => Get (Get (Result, "file")),
                  Line   => Get (Get (Result, "line")),
                  Column => Get (Get (Result, "col")));
            else
               Add_Flow_Result
                 (Unit  => Unit,
                  Subp  => Subp,
                  Error => Severe = "error");
            end if;
         end;
      end loop;
   end Handle_Flow_File;

   -----------------------
   -- Handle_Proof_File --
   -----------------------

   procedure Handle_Proof_File (Fn : String) is
      use GNATCOLL.JSON;
      Dict : constant JSON_Value := Read (Read_File_Into_String (Fn), Fn);
      Unit : constant Unit_Type := Mk_Unit (Ada.Directories.Base_Name (Fn));
      Entries : constant JSON_Array := Get (Dict);
   begin
      for Index in 1 .. Length (Entries) loop
         declare
            Result : constant JSON_Value := Get (Entries, Index);
            Severe : constant String     := Get (Get (Result, "severity"));
         begin
            Add_Proof_Result
              (Unit   => Unit,
               Subp   => Mk_Subp_Of_Entity (Get (Result, "entity")),
               Proved => Severe = "info");
         end;
      end loop;
   end Handle_Proof_File;

   -----------------------
   -- Handle_SPARK_File --
   -----------------------

   procedure Handle_SPARK_File
     (Fn               : String;
      No_Analysis_Done : out Boolean)
   is
      use GNATCOLL.JSON;
      Dict : constant JSON_Value := Read (Read_File_Into_String (Fn), Fn);
      Basename : constant String := Ada.Directories.Base_Name (Fn);
      Unit : constant Unit_Type := Mk_Unit (Basename);
      Has_Flow : constant Boolean :=
        Ada.Directories.Exists
          (Ada.Directories.Compose (Name      => Basename,
                                    Extension => VC_Kinds.Flow_Suffix));
      Has_Proof : constant Boolean :=
        Ada.Directories.Exists
          (Ada.Directories.Compose (Name      => Basename,
                                    Extension => VC_Kinds.Proof_Suffix));

      --  Status of analysis performed on all subprograms and packages of a
      --  unit depend on presence of a file <unit>.flow and <unit>.proof in
      --  the same directory as the file <unit>.spark.

      --  This status is only relevant for subprograms and packages which are
      --  in SPARK. Also, we do not currently take into account the fact that
      --  possibly a single subprogram/line in the unit was analyzed.

      Analysis : constant Analysis_Status :=
        (if Has_Flow and Has_Proof then Flow_And_Proof
         elsif Has_Flow then Flow_Analysis
         elsif Has_Proof then Proof_Only
         else No_Analysis);

   begin
      No_Analysis_Done := True;

      declare
         Entries : constant JSON_Array := Get (Dict);
      begin
         for Index in 1 .. Length (Entries) loop
            declare
               Result   : constant JSON_Value := Get (Entries, Index);
               In_SPARK : constant Boolean :=
                 Get (Get (Result, "spark")) = "all";
            begin
               Add_SPARK_Status
                 (Unit         => Unit,
                  Subp         => Mk_Subp_Of_Entity (Result),
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
      end;
   end Handle_SPARK_File;

   -----------------------
   -- Handle_Source_Dir --
   -----------------------

   procedure Handle_Source_Dir (Dir : String) is

      No_Analysis_Done : Boolean := True;
      --  Set to True if no analysis was performed at all

      procedure Local_Handle_SPARK_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Wrapper for Handle_SPARK_File

      procedure Local_Handle_Flow_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Wrapper for Handle_Flow_File

      procedure Local_Handle_Proof_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Wrapper for Handle_Proof_File

      ----------------------------
      -- Local_Handle_Flow_File --
      ----------------------------

      procedure Local_Handle_Flow_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_Flow_File (Item);
      end Local_Handle_Flow_File;

      -----------------------------
      -- Local_Handle_Proof_File --
      -----------------------------

      procedure Local_Handle_Proof_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean) is
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_Proof_File (Item);
      end Local_Handle_Proof_File;

      -----------------------------
      -- Local_Handle_SPARK_File --
      -----------------------------

      procedure Local_Handle_SPARK_File
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean)
      is
         Local_No_Analysis_Done : Boolean;
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);
         Handle_SPARK_File (Item, Local_No_Analysis_Done);
         No_Analysis_Done := No_Analysis_Done and Local_No_Analysis_Done;
      end Local_Handle_SPARK_File;

      procedure Iterate_SPARK is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_SPARK_File);

      procedure Iterate_Flow is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_Flow_File);

      procedure Iterate_Proof is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
          (Action => Local_Handle_Proof_File);

      Save_Dir : constant String := Ada.Directories.Current_Directory;

   --  Start of Handle_Source_Dir

   begin
      Ada.Directories.Set_Directory (Dir);
      Iterate_SPARK (Path => "*." & VC_Kinds.SPARK_Suffix);

      if No_Analysis_Done then
         Reset_All_Results;
      else
         Iterate_Flow (Path => "*." & VC_Kinds.Flow_Suffix);
         Iterate_Proof (Path => "*." & VC_Kinds.Proof_Suffix);
      end if;

      Ada.Directories.Set_Directory (Save_Dir);
   exception
      when others =>
         Ada.Directories.Set_Directory (Save_Dir);
         raise;
   end Handle_Source_Dir;

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
                 "  " & Subp_Name (Subp) & " at " & Subp_File (Subp) & ":" &
                   Int_Image (Subp_Line (Subp)));

            if Stat.SPARK then
               if Stat.Analysis = No_Analysis then
                  Put_Line (Handle, " not analyzed");
               else
                  if Stat.Analysis in Flow_Analysis | Flow_And_Proof then
                     Put (Handle,
                          " flow analyzed ("
                          & Int_Image (Stat.Flow_Errors) & " errors and "
                          & Int_Image (Stat.Flow_Warnings) & " warnings)");
                  end if;

                  if Stat.Analysis = Flow_And_Proof then
                     Put (Handle, " and");
                  end if;

                  if Stat.Analysis in Proof_Only | Flow_And_Proof then
                     if Stat.VC_Count = Stat.VC_Proved then
                        Put (Handle,
                             " proved ("
                             & Int_Image (Stat.VC_Count) & " checks)");
                     else
                        Put (Handle,
                             " not proved," & Stat.VC_Proved'Img
                             & " checks out of" & Stat.VC_Count'Img
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
                                    ":" & Int_Image (Msg.Line) & ":" &
                                    Int_Image (Msg.Column) & ": " &
                                    Ada.Strings.Unbounded.To_String
                                    (Msg.Reason));
                     end loop;
                  end if;
               end if;
            else
               Put_Line (Handle, " skipped");
            end if;
         end For_Each_Subp;

      begin
         Put_Line (Handle,
                   "in unit " & Unit_Name (Unit) & ", "
                   & Int_Image (Num_Subps_SPARK (Unit))
                   & " subprograms and packages out of "
                   & Int_Image (Num_Subps (Unit)) & " analyzed");
         Iter_Unit_Subps (Unit, For_Each_Subp'Access, Ordered => True);
      end For_Each_Unit;

      N_Un : constant Integer := Num_Units;

   --  Start of Print_Analysis_Report

   begin
      if N_Un > 0 then
         Put_Line (Handle, "Analyzed" & N_Un'Img & " units");
         Iter_Units (For_Each_Unit'Access, Ordered => True);
      end if;
   end Print_Analysis_Report;

   procedure Iterate_Source_Dirs is new For_Line_In_File (Handle_Source_Dir);

   Source_Directories_File : GNAT.OS_Lib.String_Access;

   use Ada.Text_IO;

   Handle : File_Type;

   --  Start of SPARK_Report

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Abort_With_Message ("No source directory file given, aborting");
   end if;
   Source_Directories_File := new String'(Ada.Command_Line.Argument (1));
   Iterate_Source_Dirs (Source_Directories_File.all);
   Create (Handle,
           Out_File,
           Configuration.SPARK_Report_File
             (GNAT.Directory_Operations.Dir_Name
                (Source_Directories_File.all)));
   Print_Analysis_Report (Handle);
   Close (Handle);
end SPARK_Report;
