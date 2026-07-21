------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                     M A N I F E S T _ G E N E R A T O R                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
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

with Ada.Characters.Handling;
with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Containers.Indefinite_Vectors;
with Ada.Directories;
with Ada.Exceptions;        use Ada.Exceptions;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;

with Call;          use Call;
with Configuration; use Configuration;
with GNATCOLL.JSON; use GNATCOLL.JSON;
with GPR2.Build.Compilation_Unit;
with SPARK_Artifacts;
with SPARK_JSON_Entities;
with String_Utils;  use String_Utils;

package body Manifest_Generator is

   Manifest_Version : constant := 1;
   --  Proof manifest format version targeted by this generator

   Entry_Penalty : constant := 5_000;
   --  Heuristic: when choosing a unit default step limit, count one explicit
   --  rule as roughly this many replay steps. This intentionally
   --  accepts a somewhat larger default when it avoids many local entries.

   Selection_Hysteresis : constant := 1_000;
   --  Keep the current default-prover heuristic when another candidate's
   --  replay score is only marginally better.

   package Prover_Steps_Maps is new
     Ada.Containers.Indefinite_Ordered_Maps
       (Key_Type     => String,
        Element_Type => Natural);

   type Leaf_Info is record
      Provers : Prover_Steps_Maps.Map;
      --  Maps each prover that proved this leaf to the steps it needed
   end record;

   package Leaf_Vectors is new
     Ada.Containers.Indefinite_Vectors
       (Index_Type   => Positive,
        Element_Type => Leaf_Info);

   type Proof_Entity_Info is record
      Identity : SPARK_JSON_Entities.Entity_Info;
      Leaves   : Leaf_Vectors.Vector;
   end record;

   package Entity_Vectors is new
     Ada.Containers.Indefinite_Vectors
       (Index_Type   => Positive,
        Element_Type => Proof_Entity_Info);

   type Unit_Proof_Data is record
      SPARK_File : Unbounded_String;
      Unit_Path  : Unbounded_String;
      Entities   : Entity_Vectors.Vector;
   end record;

   type Manifest_Entry is record
      Path         : Unbounded_String;
      Kind         : Unbounded_String;
      Profile      : Unbounded_String;
      Provers      : String_Lists.List;
      Steps        : Natural := 0;
      Hierarchical : Boolean := True;
      --  False for an entry that applies to its anchor entity only. Used for
      --  the unit's own entity, which shares the bare unit path with the
      --  generated unit default and must not compete with it over the
      --  entities the default covers hierarchically.
   end record;

   package Entry_Vectors is new
     Ada.Containers.Indefinite_Vectors
       (Index_Type   => Positive,
        Element_Type => Manifest_Entry);

   type Candidate_Score is record
      Total            : Natural := 0;
      Replay_Budget    : Natural := 0;
      Explicit_Entries : Natural := 0;
      Prover_Count     : Natural := 0;
      Default_Steps    : Natural := 0;
   end record;

   type Manifest_Candidate is record
      Default_Provers : String_Lists.List;
      Entries         : Entry_Vectors.Vector;
      Score           : Candidate_Score;
   end record;

   procedure Add_Leaf
     (Data       : in out Unit_Proof_Data;
      Entity_Key : Positive;
      Entity     : SPARK_JSON_Entities.Entity_Info;
      Leaf       : JSON_Value);
   --  Record the successful provers and steps of one proof leaf, creating
   --  the entity entry on first encounter.

   function Belongs_To_Unit
     (Data : Unit_Proof_Data; Path : String) return Boolean;
   --  Return True if the entity at Path lives in the unit being generated

   function Build_Candidate
     (Data            : Unit_Proof_Data;
      Default_Provers : String_Lists.List;
      Emit_Warnings   : Boolean := True) return Manifest_Candidate;
   --  Build a generated manifest candidate from the selected unit default

   function Canonical_Prover (Name : String) return String;
   --  Normalize prover names to the spelling used in proof manifests

   function Choose_Default_Prover
     (Data : Unit_Proof_Data) return String_Lists.List;
   --  Pick the single concrete prover used as the unit default

   function Choose_Default_Steps
     (Data : Unit_Proof_Data; Default_Provers : String_Lists.List)
      return Natural;
   --  Pick the unit default step limit for the chosen default provers

   function Choose_Entry_Provers
     (Leaves : Leaf_Vectors.Vector) return String_Lists.List;
   --  Compute the prover list for an explicit entry covering Leaves

   function Choose_Manifest_Candidate
     (Data : Unit_Proof_Data) return Manifest_Candidate;
   --  Enumerate default prover candidates and pick the selected manifest

   function Covers_All
     (Leaves : Leaf_Vectors.Vector; Provers : String_Lists.List)
      return Boolean;

   function Default_Prover_Candidates
     (Data : Unit_Proof_Data) return String_Lists.List;
   --  Return each concrete prover that proves at least one leaf

   function Display_Unit_Path (Data : Unit_Proof_Data) return String;
   --  Return the Ada-cased unit path used in generated manifest entries

   function Entity_Count
     (Data : Unit_Proof_Data; Name : String) return Natural;
   --  Return how many collected entities share the given name

   function Entry_For
     (Data            : Unit_Proof_Data;
      Entity          : Proof_Entity_Info;
      Default_Provers : String_Lists.List) return Manifest_Entry;
   --  Build the manifest entry describing Entity

   procedure Generate_One
     (SPARK_File : String; Unit_Name : String; Output_Dir : String);
   --  Generate the manifest for the unit named Unit_Name whose proof data is
   --  in SPARK_File.

   function Has_Entry
     (Data            : Unit_Proof_Data;
      Entity          : Proof_Entity_Info;
      Default_Provers : String_Lists.List;
      Default_Steps   : Natural;
      Emit_Warnings   : Boolean := True) return Boolean;
   --  Return True if Entity needs an explicit entry beyond the unit default

   function Max_Success_Steps
     (Leaves : Leaf_Vectors.Vector; Provers : String_Lists.List)
      return Natural;
   --  Return the largest step count among Leaves proved by Provers

   function Output_File
     (Data : Unit_Proof_Data; Output_Dir : String) return String;
   --  Return the TOML output path for Data

   procedure Process_Check_Tree
     (Data       : in out Unit_Proof_Data;
      Entity_Key : Positive;
      Entity     : SPARK_JSON_Entities.Entity_Info;
      Node       : JSON_Value);
   --  Walk a check tree, recording each proof leaf it contains

   function Prover_Less (Left, Right : String) return Boolean;

   procedure Read_Proof
     (Data         : in out Unit_Proof_Data;
      Proof        : JSON_Value;
      Entity_Table : SPARK_JSON_Entities.Entity_Vectors.Vector);
   --  Process one proof object, resolving its entity and check tree

   function Read_Unit_Proof_Data
     (SPARK_File : String; Unit_Name : String) return Unit_Proof_Data;
   --  Read and normalize manifest-relevant proof data from SPARK_File, tagging
   --  it with the dotted (lower-case) Ada unit name Unit_Name.

   function Rounded_Steps (Steps : Natural) return Natural;

   function Score_Default
     (Data            : Unit_Proof_Data;
      Default_Provers : String_Lists.List;
      Default_Steps   : Natural) return Candidate_Score;
   --  Score the manifest implied by Default_Provers and Default_Steps

   function Score_Less (Left, Right : Candidate_Score) return Boolean;
   --  Return True if Left is preferred over Right

   function Score_Wins
     (Left : Candidate_Score; Baseline : Candidate_Score) return Boolean;
   --  Return True if Left beats Baseline by the hysteresis margin

   procedure Sort_Entries (Entries : in out Entry_Vectors.Vector);
   --  Sort manifest entries into a stable order for deterministic output

   procedure Sort_Entities (Entities : in out Entity_Vectors.Vector);
   --  Sort collected entities into a stable order

   function TOML_String (S : String) return String;

   function Valid_Manifest_Path (Path : String) return Boolean;

   procedure Write_Manifest
     (Data       : Unit_Proof_Data;
      Output_Dir : String;
      Entries    : Entry_Vectors.Vector);
   --  Write the TOML manifest file for the collected entries

   ----------------------
   -- Canonical_Prover --
   ----------------------

   function Canonical_Prover (Name : String) return String is
      Lower : constant String := Ada.Characters.Handling.To_Lower (Name);
   begin
      if Lower = "altergo" or else Lower = "alt-ergo" then
         return "alt-ergo";
      else
         return Lower;
      end if;
   end Canonical_Prover;

   ----------------
   -- Covers_All --
   ----------------

   function Covers_All
     (Leaves : Leaf_Vectors.Vector; Provers : String_Lists.List) return Boolean
   is
   begin
      for Leaf of Leaves loop
         if not Leaf.Provers.Contains ("trivial") then
            declare
               Covered : Boolean := False;
            begin
               for Prover of Provers loop
                  if Leaf.Provers.Contains (Prover) then
                     Covered := True;
                     exit;
                  end if;
               end loop;

               if not Covered then
                  return False;
               end if;
            end;
         end if;
      end loop;

      return True;
   end Covers_All;

   --------------
   -- Generate --
   --------------

   procedure Generate (Units : Gnatprove_Build.Unit_Set; Output_Dir : String)
   is
   begin
      Create_Path_Or_Exit (Output_Dir);

      for Unit of Units loop
         declare
            SPARK_File : constant String :=
              SPARK_Artifacts.SPARK_File_For_Unit (Unit);
            Unit_Name  : constant String :=
              Ada.Characters.Handling.To_Lower (String (Unit.Name));
         begin
            if Ada.Directories.Exists (SPARK_File) then
               Generate_One (SPARK_File, Unit_Name, Output_Dir);
            end if;
         end;
      end loop;
   end Generate;

   ------------------
   -- Generate_One --
   ------------------

   procedure Generate_One
     (SPARK_File : String; Unit_Name : String; Output_Dir : String)
   is
      Data : Unit_Proof_Data;
   begin
      Data := Read_Unit_Proof_Data (SPARK_File, Unit_Name);

      if Data.Entities.Is_Empty then
         Write_Manifest (Data, Output_Dir, Entry_Vectors.Empty_Vector);
         return;
      end if;

      Sort_Entities (Data.Entities);

      declare
         Candidate : constant Manifest_Candidate :=
           Choose_Manifest_Candidate (Data);
      begin
         Write_Manifest (Data, Output_Dir, Candidate.Entries);
      end;
   exception
      when E : others =>
         --  A malformed or unexpected .spark file must not abort the whole
         --  run: the analysis already succeeded and its report still has to be
         --  produced. Warn and skip this file's manifest instead.
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "warning: cannot generate proof manifest from "
            & SPARK_File
            & ": "
            & Exception_Message (E));
   end Generate_One;

   ---------------------
   -- Belongs_To_Unit --
   ---------------------

   function Belongs_To_Unit
     (Data : Unit_Proof_Data; Path : String) return Boolean
   is
      Lower_Path : constant String := Ada.Characters.Handling.To_Lower (Path);
      Unit       : constant String := To_String (Data.Unit_Path);
   begin
      return
        Lower_Path = Unit
        or else
          (Lower_Path'Length > Unit'Length
           and then
             Lower_Path
               (Lower_Path'First .. Lower_Path'First + Unit'Length - 1)
             = Unit
           and then Lower_Path (Lower_Path'First + Unit'Length) = '.');
   end Belongs_To_Unit;

   ---------------------
   -- Build_Candidate --
   ---------------------

   function Build_Candidate
     (Data            : Unit_Proof_Data;
      Default_Provers : String_Lists.List;
      Emit_Warnings   : Boolean := True) return Manifest_Candidate
   is
      Result : Manifest_Candidate;
   begin
      Result.Default_Provers := Default_Provers;

      if not Default_Provers.Is_Empty then
         declare
            Root          : constant String := Display_Unit_Path (Data);
            Default_Steps : constant Natural :=
              Choose_Default_Steps (Data, Default_Provers);
            Root_Entry    : constant Manifest_Entry :=
              (Path         => To_Unbounded_String (Root),
               Kind         => Null_Unbounded_String,
               Profile      => Null_Unbounded_String,
               Provers      => Default_Provers,
               Steps        => Default_Steps,
               Hierarchical => True);
         begin
            Result.Score :=
              Score_Default (Data, Default_Provers, Default_Steps);
            Result.Entries.Append (Root_Entry);

            for Entity of Data.Entities loop
               if Has_Entry
                    (Data,
                     Entity,
                     Default_Provers,
                     Default_Steps,
                     Emit_Warnings)
               then
                  declare
                     Item : Manifest_Entry :=
                       Entry_For (Data, Entity, Default_Provers);
                  begin
                     if not Item.Provers.Is_Empty then
                        --  The unit's own entity shares the bare unit path
                        --  used by the generated unit default. Emit it as a
                        --  non-hierarchical entry carrying its kind, so it
                        --  overrides the default for that entity alone and
                        --  does not compete with the default over the
                        --  entities the default covers hierarchically. The
                        --  kind keeps the entry distinct from the bare-path
                        --  default when read back.
                        if Ada.Characters.Handling.To_Lower
                             (To_String (Item.Path))
                          = Ada.Characters.Handling.To_Lower (Root)
                        then
                           Item.Hierarchical := False;
                           if Length (Item.Kind) = 0 then
                              Item.Kind := Entity.Identity.Manifest_Kind;
                           end if;
                        end if;

                        Result.Entries.Append (Item);
                     end if;
                  end;
               end if;
            end loop;

            Sort_Entries (Result.Entries);
         end;
      end if;

      return Result;
   end Build_Candidate;

   --------------
   -- Add_Leaf --
   --------------

   procedure Add_Leaf
     (Data       : in out Unit_Proof_Data;
      Entity_Key : Positive;
      Entity     : SPARK_JSON_Entities.Entity_Info;
      Leaf       : JSON_Value)
   is
      Attempts : constant JSON_Value := Get (Leaf, "proof_attempts");
      Info     : Leaf_Info;

      procedure Read_Attempt (Name : UTF8_String; Attempt : JSON_Value);

      ------------------
      -- Read_Attempt --
      ------------------

      procedure Read_Attempt (Name : UTF8_String; Attempt : JSON_Value) is
      begin
         if Has_Field (Attempt, "result")
           and then String'(Get (Attempt, "result")) = "Valid"
         then
            declare
               Prover : constant String := Canonical_Prover (Name);
               Steps  : constant Natural :=
                 (if Has_Field (Attempt, "steps")
                  then Natural'(Get (Attempt, "steps"))
                  else 0);
               Cur    : constant Prover_Steps_Maps.Cursor :=
                 Info.Provers.Find (Prover);
            begin
               --  Keep the largest step count seen for this prover, so the
               --  per-prover figure stays a safe replay budget for it.
               if Prover_Steps_Maps.Has_Element (Cur) then
                  Info.Provers.Replace_Element
                    (Cur,
                     Natural'Max (Prover_Steps_Maps.Element (Cur), Steps));
               else
                  Info.Provers.Insert (Prover, Steps);
               end if;
            end;
         end if;
      end Read_Attempt;

   begin
      Map_JSON_Object (Attempts, Read_Attempt'Access);

      if Info.Provers.Is_Empty then
         return;
      end if;

      for E of Data.Entities loop
         if E.Identity.Key_Index = Entity_Key then
            E.Leaves.Append (Info);
            return;
         end if;
      end loop;

      declare
         New_Entity : Proof_Entity_Info;
         Name       : constant String := To_String (Entity.Name);
      begin
         if not Belongs_To_Unit (Data, Name) then
            return;
         end if;

         New_Entity.Identity := Entity;
         New_Entity.Leaves.Append (Info);
         Data.Entities.Append (New_Entity);
      end;
   end Add_Leaf;

   ---------------------------
   -- Choose_Default_Prover --
   ---------------------------

   function Choose_Default_Prover
     (Data : Unit_Proof_Data) return String_Lists.List
   is
      Candidates : constant String_Lists.List :=
        Default_Prover_Candidates (Data);
      Result     : String_Lists.List;
      Best       : Unbounded_String;
      Best_Count : Natural := 0;
   begin
      --  Heuristic: use one concrete prover as the unit default. The
      --  selected prover is the one proving the most leaves in this .spark
      --  file; ties use a stable preference order for deterministic diffs.
      for Candidate of Candidates loop
         declare
            Count : Natural := 0;
         begin
            for Entity of Data.Entities loop
               for Leaf of Entity.Leaves loop
                  if Leaf.Provers.Contains (Candidate) then
                     Count := Count + 1;
                  end if;
               end loop;
            end loop;

            if Count > Best_Count
              or else
                (Count = Best_Count
                 and then
                   (Length (Best) = 0
                    or else Prover_Less (Candidate, To_String (Best))))
            then
               Best := To_Unbounded_String (Candidate);
               Best_Count := Count;
            end if;
         end;
      end loop;

      if Length (Best) > 0 then
         Result.Append (To_String (Best));
      end if;
      return Result;
   end Choose_Default_Prover;

   -------------------------------
   -- Choose_Manifest_Candidate --
   -------------------------------

   function Choose_Manifest_Candidate
     (Data : Unit_Proof_Data) return Manifest_Candidate
   is
      Baseline_Provers : constant String_Lists.List :=
        Choose_Default_Prover (Data);
      Baseline         : constant Manifest_Candidate :=
        Build_Candidate (Data, Baseline_Provers, Emit_Warnings => False);
      Best             : Manifest_Candidate := Baseline;
   begin
      for Prover of Default_Prover_Candidates (Data) loop
         declare
            Candidate_Provers : String_Lists.List;
         begin
            if not Baseline_Provers.Contains (Prover) then
               Candidate_Provers.Append (Prover);

               declare
                  Candidate : constant Manifest_Candidate :=
                    Build_Candidate
                      (Data, Candidate_Provers, Emit_Warnings => False);
               begin
                  if Score_Less (Candidate.Score, Best.Score) then
                     Best := Candidate;
                  end if;
               end;
            end if;
         end;
      end loop;

      if Score_Wins (Best.Score, Baseline.Score) then
         return Build_Candidate (Data, Best.Default_Provers);
      else
         return Build_Candidate (Data, Baseline.Default_Provers);
      end if;
   end Choose_Manifest_Candidate;

   --------------------------
   -- Choose_Default_Steps --
   --------------------------

   function Choose_Default_Steps
     (Data : Unit_Proof_Data; Default_Provers : String_Lists.List)
      return Natural
   is
      Candidates : String_Lists.List;
      Best       : Natural := 1_000;
      Best_Score : Candidate_Score;
      Have_Best  : Boolean := False;
   begin
      --  Heuristic: try only readable rounded step buckets already needed
      --  by entities covered by the default prover. Choose the bucket that
      --  minimizes replay step budget plus Entry_Penalty per explicit
      --  entry, favoring fewer entries and stable diffs over tiny defaults.
      for Entity of Data.Entities loop
         if Covers_All (Entity.Leaves, Default_Provers) then
            declare
               Candidate : constant String :=
                 Ada.Strings.Fixed.Trim
                   (Natural'Image
                      (Rounded_Steps
                         (Max_Success_Steps (Entity.Leaves, Default_Provers))),
                    Ada.Strings.Left);
            begin
               if not Candidates.Contains (Candidate) then
                  Candidates.Append (Candidate);
               end if;
            end;
         end if;
      end loop;

      for Candidate_Image of Candidates loop
         declare
            Candidate : constant Natural := Natural'Value (Candidate_Image);
            Score     : constant Candidate_Score :=
              Score_Default (Data, Default_Provers, Candidate);
         begin
            if not Have_Best or else Score_Less (Score, Best_Score) then
               Best := Candidate;
               Best_Score := Score;
               Have_Best := True;
            end if;
         end;
      end loop;

      return Best;
   end Choose_Default_Steps;

   -------------------------------
   -- Default_Prover_Candidates --
   -------------------------------

   function Default_Prover_Candidates
     (Data : Unit_Proof_Data) return String_Lists.List
   is
      Result : String_Lists.List;
   begin
      for Entity of Data.Entities loop
         for Leaf of Entity.Leaves loop
            for Cur in Leaf.Provers.Iterate loop
               declare
                  Prover : constant String := Prover_Steps_Maps.Key (Cur);
               begin
                  if Prover /= "trivial" and then not Result.Contains (Prover)
                  then
                     Result.Append (Prover);
                  end if;
               end;
            end loop;
         end loop;
      end loop;

      return Result;
   end Default_Prover_Candidates;

   -----------------------
   -- Display_Unit_Path --
   -----------------------

   function Display_Unit_Path (Data : Unit_Proof_Data) return String is
      Unit : constant String := To_String (Data.Unit_Path);
   begin
      for Entity of Data.Entities loop
         declare
            Path       : constant String := To_String (Entity.Identity.Name);
            Lower_Path : constant String :=
              Ada.Characters.Handling.To_Lower (Path);
         begin
            if Lower_Path = Unit
              or else
                (Lower_Path'Length > Unit'Length
                 and then
                   Lower_Path
                     (Lower_Path'First .. Lower_Path'First + Unit'Length - 1)
                   = Unit
                 and then Lower_Path (Lower_Path'First + Unit'Length) = '.')
            then
               return Path (Path'First .. Path'First + Unit'Length - 1);
            end if;
         end;
      end loop;

      return Standard_Ada_Case (Unit);
   end Display_Unit_Path;

   --------------------------
   -- Choose_Entry_Provers --
   --------------------------

   function Choose_Entry_Provers
     (Leaves : Leaf_Vectors.Vector) return String_Lists.List
   is
      Result : String_Lists.List;

      function Best_Next_Prover (Covered_By : String_Lists.List) return String;
      --  Return the concrete prover covering the most uncovered leaves

      function Coverage_Count (Prover : String) return Natural;
      --  Count how many leaves Prover can prove

      function Is_Better
        (Prover     : String;
         Count      : Natural;
         Best       : Unbounded_String;
         Best_Count : Natural) return Boolean;
      --  Return True when Prover is a better greedy choice than Best

      function Needs_Coverage
        (Leaf : Leaf_Info; Covered_By : String_Lists.List) return Boolean;
      --  Return True when Leaf is non-trivial and not covered yet

      ----------------------
      -- Best_Next_Prover --
      ----------------------

      function Best_Next_Prover (Covered_By : String_Lists.List) return String
      is
         Best       : Unbounded_String;
         Best_Count : Natural := 0;
      begin
         for Leaf of Leaves loop
            if Needs_Coverage (Leaf, Covered_By) then
               for Cur in Leaf.Provers.Iterate loop
                  declare
                     Prover : constant String := Prover_Steps_Maps.Key (Cur);
                     Count  : constant Natural := Coverage_Count (Prover);
                  begin
                     if Prover /= "trivial"
                       and then not Covered_By.Contains (Prover)
                       and then Is_Better (Prover, Count, Best, Best_Count)
                     then
                        Best := To_Unbounded_String (Prover);
                        Best_Count := Count;
                     end if;
                  end;
               end loop;
            end if;
         end loop;

         return To_String (Best);
      end Best_Next_Prover;

      --------------------
      -- Coverage_Count --
      --------------------

      function Coverage_Count (Prover : String) return Natural is
         Result : Natural := 0;
      begin
         for Leaf of Leaves loop
            if Leaf.Provers.Contains (Prover) then
               Result := Result + 1;
            end if;
         end loop;
         return Result;
      end Coverage_Count;

      ---------------
      -- Is_Better --
      ---------------

      function Is_Better
        (Prover     : String;
         Count      : Natural;
         Best       : Unbounded_String;
         Best_Count : Natural) return Boolean is
      begin
         return
           Count > Best_Count
           or else
             (Count = Best_Count
              and then
                (Length (Best) = 0
                 or else Prover_Less (Prover, To_String (Best))));
      end Is_Better;

      --------------------
      -- Needs_Coverage --
      --------------------

      function Needs_Coverage
        (Leaf : Leaf_Info; Covered_By : String_Lists.List) return Boolean is
      begin
         if Leaf.Provers.Contains ("trivial") then
            return False;
         end if;

         for Prover of Covered_By loop
            if Leaf.Provers.Contains (Prover) then
               return False;
            end if;
         end loop;

         return True;
      end Needs_Coverage;

   begin
      --  Heuristic: explicit entries use a greedy cover of successful
      --  concrete provers. This keeps prover lists small without trying to
      --  solve a global minimization problem for the manifest.
      loop
         exit when Covers_All (Leaves, Result);

         declare
            Prover : constant String := Best_Next_Prover (Result);
         begin
            exit when Prover = "";
            Result.Append (Prover);
         end;
      end loop;

      return Result;
   end Choose_Entry_Provers;

   ------------------
   -- Entity_Count --
   ------------------

   function Entity_Count (Data : Unit_Proof_Data; Name : String) return Natural
   is
      Count : Natural := 0;
   begin
      for Entity of Data.Entities loop
         if To_String (Entity.Identity.Name) = Name then
            Count := Count + 1;
         end if;
      end loop;
      return Count;
   end Entity_Count;

   ---------------
   -- Entry_For --
   ---------------

   function Entry_For
     (Data            : Unit_Proof_Data;
      Entity          : Proof_Entity_Info;
      Default_Provers : String_Lists.List) return Manifest_Entry
   is
      Default_Covers : constant Boolean :=
        Covers_All (Entity.Leaves, Default_Provers);
      Provers        : constant String_Lists.List :=
        (if Default_Covers
         then Default_Provers
         else Choose_Entry_Provers (Entity.Leaves));
      Result         : Manifest_Entry;
   begin
      Result.Path := Entity.Identity.Name;
      Result.Provers := Provers;
      Result.Steps :=
        Rounded_Steps (Max_Success_Steps (Entity.Leaves, Provers));

      --  Explicit entries only need kind/profile when the path alone is
      --  ambiguous. The caller handles the special unit-root entry that shares
      --  the bare path with the generated default.
      if Entity_Count (Data, To_String (Entity.Identity.Name)) > 1 then
         Result.Kind := Entity.Identity.Manifest_Kind;
         Result.Profile := Entity.Identity.Manifest_Profile;
      end if;

      return Result;
   end Entry_For;

   ---------------
   -- Has_Entry --
   ---------------

   function Has_Entry
     (Data            : Unit_Proof_Data;
      Entity          : Proof_Entity_Info;
      Default_Provers : String_Lists.List;
      Default_Steps   : Natural;
      Emit_Warnings   : Boolean := True) return Boolean
   is
      Default_Covers : constant Boolean :=
        Covers_All (Entity.Leaves, Default_Provers);
   begin
      if Default_Covers
        and then
          Rounded_Steps (Max_Success_Steps (Entity.Leaves, Default_Provers))
          <= Default_Steps
      then
         return False;
      end if;

      --  Heuristic: overloaded entities without manifest_profile are not
      --  emitted as explicit entries because the matcher could not distinguish
      --  them reliably.
      if Entity_Count (Data, To_String (Entity.Identity.Name)) > 1
        and then Length (Entity.Identity.Manifest_Profile) = 0
      then
         if Emit_Warnings then
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: "
               & To_String (Entity.Identity.Name)
               & " in "
               & To_String (Data.SPARK_File)
               & " is overloaded but lacks manifest metadata");
         end if;
         return False;
      end if;

      --  Skip entities whose path is not a plain dot-separated Ada name,
      --  such as user-defined operators: the manifest reader rejects such
      --  paths, so emitting one would make the generated manifest
      --  unreadable. Their requirements fall back to the unit default.
      if not Valid_Manifest_Path (To_String (Entity.Identity.Name)) then
         if Emit_Warnings then
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: "
               & To_String (Entity.Identity.Name)
               & " in "
               & To_String (Data.SPARK_File)
               & " has no plain Ada name; skipping manifest entry");
         end if;
         return False;
      end if;

      return True;
   end Has_Entry;

   -----------------------
   -- Max_Success_Steps --
   -----------------------

   function Max_Success_Steps
     (Leaves : Leaf_Vectors.Vector; Provers : String_Lists.List) return Natural
   is
      Result : Natural := 0;
   begin
      --  For each leaf, replay only needs the cheapest of the chosen
      --  provers that proved it, so take the minimum steps over those;
      --  the budget is then the maximum of those per-leaf minima.
      for Leaf of Leaves loop
         declare
            Leaf_Min : Natural := Natural'Last;
            Found    : Boolean := False;
         begin
            for Prover of Provers loop
               declare
                  Cur : constant Prover_Steps_Maps.Cursor :=
                    Leaf.Provers.Find (Prover);
               begin
                  if Prover_Steps_Maps.Has_Element (Cur) then
                     Leaf_Min :=
                       Natural'Min (Leaf_Min, Prover_Steps_Maps.Element (Cur));
                     Found := True;
                  end if;
               end;
            end loop;

            if Found then
               Result := Natural'Max (Result, Leaf_Min);
            end if;
         end;
      end loop;
      return Result;
   end Max_Success_Steps;

   -------------------
   -- Score_Default --
   -------------------

   function Score_Default
     (Data            : Unit_Proof_Data;
      Default_Provers : String_Lists.List;
      Default_Steps   : Natural) return Candidate_Score
   is
      Result : Candidate_Score :=
        (Default_Steps => Default_Steps, others => 0);

      function Prover_Count (Provers : String_Lists.List) return Natural;

      ------------------
      -- Prover_Count --
      ------------------

      function Prover_Count (Provers : String_Lists.List) return Natural is
         Result : Natural := 0;
      begin
         for Prover of Provers loop
            pragma Unreferenced (Prover);
            Result := Result + 1;
         end loop;
         return Result;
      end Prover_Count;

   begin
      for Entity of Data.Entities loop
         if Has_Entry
              (Data,
               Entity,
               Default_Provers,
               Default_Steps,
               Emit_Warnings => False)
         then
            declare
               Item : constant Manifest_Entry :=
                 Entry_For (Data, Entity, Default_Provers);
            begin
               Result.Explicit_Entries := Result.Explicit_Entries + 1;
               Result.Replay_Budget := Result.Replay_Budget + Item.Steps;
               Result.Prover_Count :=
                 Result.Prover_Count + Prover_Count (Item.Provers);
            end;
         else
            Result.Replay_Budget := Result.Replay_Budget + Default_Steps;
            Result.Prover_Count :=
              Result.Prover_Count + Prover_Count (Default_Provers);
         end if;
      end loop;

      Result.Total :=
        Result.Replay_Budget + Entry_Penalty * Result.Explicit_Entries;

      return Result;
   end Score_Default;

   ----------------
   -- Score_Less --
   ----------------

   function Score_Less (Left, Right : Candidate_Score) return Boolean is
   begin
      if Left.Total /= Right.Total then
         return Left.Total < Right.Total;
      elsif Left.Default_Steps /= Right.Default_Steps then
         return Left.Default_Steps < Right.Default_Steps;
      elsif Left.Prover_Count /= Right.Prover_Count then
         return Left.Prover_Count < Right.Prover_Count;
      else
         return Left.Explicit_Entries < Right.Explicit_Entries;
      end if;
   end Score_Less;

   ----------------
   -- Score_Wins --
   ----------------

   function Score_Wins
     (Left : Candidate_Score; Baseline : Candidate_Score) return Boolean is
   begin
      return Left.Total + Selection_Hysteresis < Baseline.Total;
   end Score_Wins;

   ------------------------
   -- Process_Check_Tree --
   ------------------------

   procedure Process_Check_Tree
     (Data       : in out Unit_Proof_Data;
      Entity_Key : Positive;
      Entity     : SPARK_JSON_Entities.Entity_Info;
      Node       : JSON_Value) is
   begin
      case Kind (Node) is
         when JSON_Array_Type  =>
            declare
               Items : constant JSON_Array := Get (Node);
            begin
               for I in 1 .. Length (Items) loop
                  Process_Check_Tree
                    (Data, Entity_Key, Entity, Get (Items, I));
               end loop;
            end;

         when JSON_Object_Type =>
            if Has_Field (Node, "proof_attempts") then
               Add_Leaf (Data, Entity_Key, Entity, Node);
            end if;

            if Has_Field (Node, "transformations") then
               declare
                  procedure Process_Transformation
                    (Name : UTF8_String; Value : JSON_Value);

                  procedure Process_Transformation
                    (Name : UTF8_String; Value : JSON_Value)
                  is
                     pragma Unreferenced (Name);
                  begin
                     Process_Check_Tree (Data, Entity_Key, Entity, Value);
                  end Process_Transformation;
               begin
                  Map_JSON_Object
                    (Get (Node, "transformations"),
                     Process_Transformation'Access);
               end;
            end if;

         when others           =>
            null;
      end case;
   end Process_Check_Tree;

   ----------------
   -- Read_Proof --
   ----------------

   procedure Read_Proof
     (Data         : in out Unit_Proof_Data;
      Proof        : JSON_Value;
      Entity_Table : SPARK_JSON_Entities.Entity_Vectors.Vector) is
   begin
      if not Has_Field (Proof, "entity")
        or else not Has_Field (Proof, "check_tree")
      then
         return;
      end if;

      declare
         Entity_Key : constant Positive := Positive'(Get (Proof, "entity"));
      begin
         for Entity of Entity_Table loop
            if Entity.Key_Index = Entity_Key then
               Process_Check_Tree
                 (Data, Entity_Key, Entity, Get (Proof, "check_tree"));
               return;
            end if;
         end loop;
      end;
   end Read_Proof;

   --------------------------
   -- Read_Unit_Proof_Data --
   --------------------------

   function Read_Unit_Proof_Data
     (SPARK_File : String; Unit_Name : String) return Unit_Proof_Data
   is
      Result : Unit_Proof_Data :=
        (SPARK_File => To_Unbounded_String (SPARK_File),
         Unit_Path  => To_Unbounded_String (Unit_Name),
         Entities   => Entity_Vectors.Empty_Vector);
      Data   : constant JSON_Value := Read_File_Into_JSON (SPARK_File);
   begin
      if not Has_Field (Data, "entities") or else not Has_Field (Data, "proof")
      then
         return Result;
      end if;

      declare
         Entity_Table : constant SPARK_JSON_Entities.Entity_Vectors.Vector :=
           SPARK_JSON_Entities.Parse_Entity_Table (Get (Data, "entities"));
         Proofs       : constant JSON_Array := Get (Data, "proof");
      begin
         for I in 1 .. Length (Proofs) loop
            Read_Proof (Result, Get (Proofs, I), Entity_Table);
         end loop;
      end;

      return Result;
   end Read_Unit_Proof_Data;

   ------------------
   -- Sort_Entries --
   ------------------

   procedure Sort_Entries (Entries : in out Entry_Vectors.Vector) is
      function Less (Left, Right : Manifest_Entry) return Boolean;

      function Less (Left, Right : Manifest_Entry) return Boolean is
      begin
         if To_String (Left.Path) /= To_String (Right.Path) then
            return To_String (Left.Path) < To_String (Right.Path);
         elsif To_String (Left.Kind) /= To_String (Right.Kind) then
            return To_String (Left.Kind) < To_String (Right.Kind);
         else
            return To_String (Left.Profile) < To_String (Right.Profile);
         end if;
      end Less;

      package Sorting is new Entry_Vectors.Generic_Sorting (Less);
   begin
      Sorting.Sort (Entries);
   end Sort_Entries;

   -------------------
   -- Sort_Entities --
   -------------------

   procedure Sort_Entities (Entities : in out Entity_Vectors.Vector) is
      function Less (Left, Right : Proof_Entity_Info) return Boolean;

      function Less (Left, Right : Proof_Entity_Info) return Boolean is
      begin
         if To_String (Left.Identity.Name) /= To_String (Right.Identity.Name)
         then
            return
              To_String (Left.Identity.Name) < To_String (Right.Identity.Name);
         else
            return
              To_String (Left.Identity.Key) < To_String (Right.Identity.Key);
         end if;
      end Less;

      package Sorting is new Entity_Vectors.Generic_Sorting (Less);
   begin
      Sorting.Sort (Entities);
   end Sort_Entities;

   -----------------
   -- Output_File --
   -----------------

   function Output_File
     (Data : Unit_Proof_Data; Output_Dir : String) return String
   is
      --  Name the file after the Ada unit, using the stem convention shared
      --  with the manifest reader: the lower-case dot-separated unit name with
      --  dots written as dashes. Deriving the stem from the unit name rather
      --  than from the source file name keeps generation correct under a
      --  non-default naming scheme, where the two differ. The lower-casing is
      --  applied here so the stem is canonical regardless of the case of the
      --  unit name reaching this point.
      Stem : String :=
        Ada.Characters.Handling.To_Lower (To_String (Data.Unit_Path));
   begin
      for C of Stem loop
         if C = '.' then
            C := '-';
         end if;
      end loop;

      return Ada.Directories.Compose (Output_Dir, Stem, "toml");
   end Output_File;

   --------------------
   -- Write_Manifest --
   --------------------

   procedure Write_Manifest
     (Data       : Unit_Proof_Data;
      Output_Dir : String;
      Entries    : Entry_Vectors.Vector)
   is
      use Ada.Text_IO;

      File : File_Type;

      procedure Put_Provers (Provers : String_Lists.List);

      -----------------
      -- Put_Provers --
      -----------------

      procedure Put_Provers (Provers : String_Lists.List) is
         First : Boolean := True;
      begin
         Put (File, "provers = [");
         for Prover of Provers loop
            if not First then
               Put (File, ", ");
            end if;
            Put (File, TOML_String (Prover));
            First := False;
         end loop;
         Put_Line (File, "]");
      end Put_Provers;

   begin
      Create_File_Or_Exit (File, Out_File, Output_File (Data, Output_Dir));
      Put_Line (File, "# Generated by gnatprove --generate-manifest-dir.");
      Put_Line
        (File,
         "version = "
         & Ada.Strings.Fixed.Trim
             (Integer'Image (Manifest_Version), Ada.Strings.Left));

      for Item of Entries loop
         New_Line (File);
         Put_Line (File, "[[rule]]");
         Put_Line (File, "path = " & TOML_String (To_String (Item.Path)));
         if Length (Item.Kind) > 0 then
            Put_Line (File, "kind = " & TOML_String (To_String (Item.Kind)));
         end if;
         if Length (Item.Profile) > 0 then
            Put_Line
              (File, "profile = " & TOML_String (To_String (Item.Profile)));
         end if;
         if not Item.Hierarchical then
            Put_Line (File, "hierarchical = false");
         end if;
         Put_Provers (Item.Provers);
         Put_Line
           (File,
            "steps = "
            & Ada.Strings.Fixed.Trim
                (Natural'Image (Item.Steps), Ada.Strings.Left));
      end loop;

      Close (File);
   end Write_Manifest;

   -----------------
   -- Prover_Less --
   -----------------

   function Prover_Less (Left, Right : String) return Boolean is
      function Rank (Prover : String) return Natural;

      function Rank (Prover : String) return Natural is
      begin
         if Prover = "z3" then
            return 0;
         elsif Prover = "cvc5" then
            return 1;
         elsif Prover = "alt-ergo" then
            return 2;
         else
            return 100;
         end if;
      end Rank;
   begin
      return
        Rank (Left) < Rank (Right)
        or else (Rank (Left) = Rank (Right) and then Left < Right);
   end Prover_Less;

   -------------------
   -- Rounded_Steps --
   -------------------

   function Rounded_Steps (Steps : Natural) return Natural is
   begin
      --  Heuristic: step values are rounded upward to coarse buckets so small
      --  prover noise does not rewrite manifests, while large values still
      --  keep enough precision to avoid excessive replay work.
      if Steps = 0 then
         return 0;
      elsif Steps <= 100 then
         return 100;
      elsif Steps <= 500 then
         return 500;
      elsif Steps <= 1_000 then
         return 1_000;
      elsif Steps <= 5_000 then
         return ((Steps + 499) / 500) * 500;
      elsif Steps <= 20_000 then
         return ((Steps + 999) / 1_000) * 1_000;
      else
         return ((Steps + 4_999) / 5_000) * 5_000;
      end if;
   end Rounded_Steps;

   -----------------
   -- TOML_String --
   -----------------

   function TOML_String (S : String) return String is
      Result : Unbounded_String := To_Unbounded_String ("""");
   begin
      for C of S loop
         if C = '\' or else C = '"' then
            Append (Result, '\');
         end if;
         Append (Result, C);
      end loop;
      Append (Result, '"');
      return To_String (Result);
   end TOML_String;

   -------------------------
   -- Valid_Manifest_Path --
   -------------------------

   function Valid_Manifest_Path (Path : String) return Boolean is
      function Is_Alpha (C : Character) return Boolean
      is ((C in 'a' .. 'z') or else (C in 'A' .. 'Z'));

      function Is_Alnum (C : Character) return Boolean
      is (Is_Alpha (C) or else C in '0' .. '9');

      At_Start : Boolean := True;
   begin
      --  Mirror the dot-separated Ada name check applied by the manifest
      --  reader, so the generator never emits an explicit entry whose path
      --  the reader would reject, such as a user-defined operator.
      for C of Path loop
         if At_Start then
            if not Is_Alpha (C) then
               return False;
            end if;
            At_Start := False;
         elsif C = '.' then
            At_Start := True;
         elsif not (Is_Alnum (C) or else C = '_') then
            return False;
         end if;
      end loop;

      return not At_Start;
   end Valid_Manifest_Path;

end Manifest_Generator;
