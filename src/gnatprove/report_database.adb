------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
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

with Ada.Containers;
with Ada.Containers.Hashed_Maps;

package body Report_Database is

   package Subp_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Subp_Type,
        Element_Type    => Stat_Rec,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Default_Stat : constant Stat_Rec :=
     Stat_Rec'
       (SPARK           => Not_In_SPARK,
        Suppr_Checks    => Check_Lists.Empty_List,
        Pragma_Assumes  => Pragma_Assume_Lists.Empty_List,
        Flow_Warnings   => 0,
        Flow_Errors     => 0,
        Flow_Checks     => 0,
        Proof_Warnings  => 0,
        Proof_Checks    => 0,
        Proof_Checks_OK => 0,
        Assumptions     => Rule_Lists.Empty_List);

   package Ordered_Subp_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Subp_Type, "<" => "<");

   type Unit_Rec is record
      Analysis    : Analysis_Progress;
      Stop_Reason : Stop_Reason_Type;
      Subps       : Subp_Maps.Map;
   end record;

   function "=" (A, B : Unit_Rec) return Boolean;
   --  Equality for objects of type Unit_Rec

   ---------
   -- "=" --
   ---------

   function "=" (A, B : Unit_Rec) return Boolean is
      use Subp_Maps;
   begin
      return A.Analysis = B.Analysis and then A.Subps = B.Subps;
   end "=";

   package Unit_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Unit_Type,
        Element_Type    => Unit_Rec,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   package Subp_Unit_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Subp_Type,
        Element_Type    => Unit_Type,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   package Ordered_Unit_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Unit_Type, "<" => "<");

   Unit_Map : Unit_Maps.Map := Unit_Maps.Empty_Map;

   Subp_Unit_Map : Subp_Unit_Maps.Map := Subp_Unit_Maps.Empty_Map;
   --  This map maps subprograms to their unit. It is filled by the
   --  Add_SPARK_Status procedure.

   Skipped_Proof          : Ordered_Subp_Sets.Set :=
     Ordered_Subp_Sets.Empty_Set;
   Skipped_Flow_And_Proof : Ordered_Subp_Sets.Set :=
     Ordered_Subp_Sets.Empty_Set;

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec));
   --  Update the stat record of the given subp using the callback. If the
   --  unit/subp do not exist yet, add them and initialize to default Stat_Rec.

   ---------------------------
   -- Add_Analysis_Progress --
   ---------------------------

   procedure Add_Analysis_Progress
     (Unit        : Unit_Type;
      Progress    : Analysis_Progress;
      Stop_Reason : Stop_Reason_Type)
   is
      C        : Unit_Maps.Cursor;
      Inserted : Boolean;
   begin
      Unit_Map.Insert
        (Unit,
         Unit_Rec'
           (Analysis    => Progress,
            Stop_Reason => Stop_Reason,
            Subps       => Subp_Maps.Empty_Map),
         C,
         Inserted);
      if not Inserted then
         Unit_Map (C).Analysis := Progress;
         Unit_Map (C).Stop_Reason := Stop_Reason;
      end if;
   end Add_Analysis_Progress;

   --------------------------------
   -- Add_Claim_With_Assumptions --
   --------------------------------

   procedure Add_Claim_With_Assumptions (Claim : Token; S : Token_Sets.Set) is

      procedure Add_Claim_Entry (Stat : in out Stat_Rec);
      --  Add the mapping claim -> assumption set to the stat record

      ---------------------
      -- Add_Claim_Entry --
      ---------------------

      procedure Add_Claim_Entry (Stat : in out Stat_Rec) is
      begin
         Stat.Assumptions.Append ((Claim => Claim, Assumptions => S));
      end Add_Claim_Entry;

      Subp : constant Subp_Type := Claim.Arg;

      --  Start of processing for Add_Claim_With_Assumptions

   begin
      Update_Subp_Entry (Subp_Unit_Map (Subp), Subp, Add_Claim_Entry'Access);
   end Add_Claim_With_Assumptions;

   ---------------------
   -- Add_Flow_Result --
   ---------------------

   procedure Add_Flow_Result
     (Unit : Unit_Type; Subp : Subp_Type; Msg_Kind : Flow_Message_Kind)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         case Msg_Kind is
            when FMK_Error =>
               Stat.Flow_Errors := Stat.Flow_Errors + 1;

            when FMK_Check =>
               Stat.Flow_Checks := Stat.Flow_Checks + 1;

            when FMK_Warning =>
               Stat.Flow_Warnings := Stat.Flow_Warnings + 1;
         end case;
      end Process;

      --  Start of processing for Add_Flow_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Flow_Result;

   ------------------------------
   -- Add_Pragma_Assume_Result --
   ------------------------------

   procedure Add_Pragma_Assume_Result
     (Unit   : Unit_Type;
      File   : String;
      Line   : Positive;
      Column : Positive;
      Subp   : Subp_Type)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.Pragma_Assumes.Append
           (Pragma_Assume'
              (File   => To_Unbounded_String (File),
               Line   => Line,
               Column => Column,
               Subp   => Subp));
      end Process;

      --  Start of processing for Add_Pragma_Assume_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Pragma_Assume_Result;

   ----------------------
   -- Add_Proof_Result --
   ----------------------

   procedure Add_Proof_Result
     (Unit : Unit_Type; Subp : Subp_Type; Proved : Boolean)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.Proof_Checks := Stat.Proof_Checks + 1;
         if Proved then
            Stat.Proof_Checks_OK := Stat.Proof_Checks_OK + 1;
         end if;
      end Process;

      --  Start of processing for Add_Proof_Result

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Proof_Result;

   procedure Add_Skip_Proof (S : Subp_Type) is
   begin
      Skipped_Proof.Include (S);
   end Add_Skip_Proof;

   procedure Add_Skip_Flow_And_Proof (S : Subp_Type) is
   begin
      Skipped_Flow_And_Proof.Include (S);
   end Add_Skip_Flow_And_Proof;

   ----------------------
   -- Add_SPARK_Status --
   ----------------------

   procedure Add_SPARK_Status
     (Unit : Unit_Type; Subp : Subp_Type; SPARK_Status : SPARK_Mode_Status)
   is

      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.SPARK := SPARK_Status;
      end Process;

      --  Start of processing for Add_SPARK_Status

   begin
      --  ??? We need to use include instead of insert because GNATprove
      --  currently mixes up packages and subprograms-acting-as packages

      Subp_Unit_Map.Include (Subp, Unit);
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_SPARK_Status;

   --------------------------
   -- Add_Suppressed_Check --
   --------------------------

   procedure Add_Suppressed_Check
     (Unit       : Unit_Type;
      Subp       : Subp_Type;
      Justif_Msg : String;
      Kind       : String;
      Reason     : String;
      File       : String;
      Line       : Positive;
      Column     : Positive)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.Suppr_Checks.Append
           (Suppressed_Check'
              (Justif_Msg => To_Unbounded_String (Justif_Msg),
               Kind       => To_Unbounded_String (Kind),
               Reason     => To_Unbounded_String (Reason),
               File       => To_Unbounded_String (File),
               Line       => Line,
               Column     => Column));
      end Process;

      --  Start of processing for Add_Suppressed_Check

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Suppressed_Check;

   -----------------------------
   -- Has_Skip_Flow_And_Proof --
   -----------------------------

   function Has_Skip_Flow_And_Proof (S : Subp_Type) return Boolean is
   begin
      return Skipped_Flow_And_Proof.Contains (S);
   end Has_Skip_Flow_And_Proof;

   --------------------
   -- Has_Skip_Proof --
   --------------------

   function Has_Skip_Proof (S : Subp_Type) return Boolean is
   begin
      return Skipped_Proof.Contains (S);
   end Has_Skip_Proof;

   --------------------
   -- Iter_All_Subps --
   --------------------

   procedure Iter_All_Subps
     (Process :
        not null access procedure
          (U : Unit_Type; Subp : Subp_Type; Stat : Stat_Rec)) is
   begin
      for Unit_C in Unit_Map.Iterate loop
         for Subp_C in Unit_Map (Unit_C).Subps.Iterate loop
            Process
              (Unit_Maps.Key (Unit_C),
               Subp_Maps.Key (Subp_C),
               Unit_Map (Unit_C).Subps (Subp_C));
         end loop;
      end loop;
   end Iter_All_Subps;

   ----------------
   -- Iter_Units --
   ----------------

   procedure Iter_Units
     (Process : not null access procedure (U : Unit_Type);
      Ordered : Boolean := False) is
   begin
      --  To iterate over units in the order of their names, first insert all
      --  unit symbols in an ordered set, and then iterate over this ordered
      --  set.

      if Ordered then
         declare
            use Ordered_Unit_Sets;
            Names : Set;
         begin
            for Unit_C in Unit_Map.Iterate loop
               Names.Insert (Unit_Maps.Key (Unit_C));
            end loop;

            for Unit of Names loop
               Process (Unit);
            end loop;
         end;

      --  Otherwise, directly iterate over map of units

      else
         for Unit_C in Unit_Map.Iterate loop
            Process (Unit_Maps.Key (Unit_C));
         end loop;
      end if;
   end Iter_Units;

   ---------------------
   -- Iter_Unit_Subps --
   ---------------------

   procedure Iter_Unit_Subps
     (Unit    : Unit_Type;
      Process :
        not null access procedure
          (Subp : Subp_Type; Stat : Stat_Rec; Progress : Analysis_Progress);
      Ordered : Boolean := False)
   is
      C : constant Unit_Maps.Cursor := Unit_Map.Find (Unit);

   begin
      if Unit_Maps.Has_Element (C) then
         --  To iterate over subprograms in the order of their names, first
         --  insert all subprogram symbols in an ordered set, and then iterate
         --  over this ordered set.

         if Ordered then
            declare
               use Ordered_Subp_Sets;
               Names : Set;
            begin
               for Subp_C in Unit_Map (C).Subps.Iterate loop
                  Names.Insert (Subp_Maps.Key (Subp_C));
               end loop;

               for Subp of Names loop
                  Process
                    (Subp, Unit_Map (C).Subps (Subp), Unit_Map (C).Analysis);
               end loop;
            end;

         --  Otherwise, directly iterate over map of units

         else
            for Subp_C in Unit_Map (C).Subps.Iterate loop
               Process
                 (Subp_Maps.Key (Subp_C),
                  Unit_Map (C).Subps (Subp_C),
                  Unit_Map (C).Analysis);
            end loop;
         end if;
      end if;
   end Iter_Unit_Subps;

   ---------------------
   -- Merge_Stat_Maps --
   ---------------------

   procedure Merge_Stat_Maps
     (A : in out Prover_Stat_Maps.Map; B : Prover_Stat_Maps.Map)
   is

      procedure Merge_Stat (A : in out Prover_Stat; B : Prover_Stat);

      ----------------
      -- Merge_Stat --
      ----------------

      procedure Merge_Stat (A : in out Prover_Stat; B : Prover_Stat) is
      begin
         A :=
           (Count     => A.Count + B.Count,
            Max_Steps => Integer'Max (A.Max_Steps, B.Max_Steps),
            Max_Time  => Float'Max (A.Max_Time, B.Max_Time));
      end Merge_Stat;

      use Prover_Stat_Maps;

      --  Start of processing for Merge_Stat_Maps

   begin
      for C in B.Iterate loop
         declare
            Position : Cursor;
            Inserted : Boolean;
         begin
            A.Insert
              (Key      => Key (C),
               New_Item => B (C),
               Position => Position,
               Inserted => Inserted);
            if not Inserted then
               Merge_Stat (A (Position), B (C));
            end if;
         end;
      end loop;
   end Merge_Stat_Maps;

   ---------------
   -- Num_Subps --
   ---------------

   function Num_Subps (Unit : Unit_Type) return Natural
   is (Natural (Unit_Map (Unit).Subps.Length));

   ---------------------
   -- Num_Subps_SPARK --
   ---------------------

   function Num_Subps_SPARK (Unit : Unit_Type) return Natural is
      Count : Natural := 0;

      procedure Update
        (Subp : Subp_Type; Stat : Stat_Rec; Progress : Analysis_Progress);

      ------------
      -- Update --
      ------------

      procedure Update
        (Subp : Subp_Type; Stat : Stat_Rec; Progress : Analysis_Progress)
      is
         pragma Unreferenced (Subp);
         pragma Unreferenced (Progress);
      begin
         if Stat.SPARK = All_In_SPARK then
            Count := Count + 1;
         end if;
      end Update;

      --  Start of processing for Num_Subps_SPARK

   begin
      Iter_Unit_Subps (Unit, Update'Access);
      return Count;
   end Num_Subps_SPARK;

   ---------------
   -- Num_Units --
   ---------------

   function Num_Units return Natural
   is (Natural (Unit_Map.Length));

   -----------------------
   -- Reset_All_Results --
   -----------------------

   procedure Reset_All_Results is
   begin
      Unit_Map.Clear;
   end Reset_All_Results;

   -------------------
   -- Unit_Progress --
   -------------------

   function Unit_Progress (Unit : Unit_Type) return Analysis_Progress is
   begin
      return Unit_Map (Unit).Analysis;
   end Unit_Progress;

   ----------------------
   -- Unit_Stop_Reason --
   ----------------------

   function Unit_Stop_Reason (Unit : Unit_Type) return Stop_Reason_Type is
   begin
      return Unit_Map (Unit).Stop_Reason;
   end Unit_Stop_Reason;

   -----------------------------------------
   -- Update_Most_Difficult_Proved_Checks --
   -----------------------------------------

   procedure Update_Most_Difficult_Proved_Checks (Check : Proved_Check) is
      use type Ada.Containers.Count_Type;
   begin
      Most_Difficult_Proved_Checks.Include (Check);

      if Most_Difficult_Proved_Checks.Length > 10 then
         Most_Difficult_Proved_Checks.Delete_First;
      end if;
   end Update_Most_Difficult_Proved_Checks;

   -----------------------
   -- Update_Subp_Entry --
   -----------------------

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec))
   is
      procedure Update_Unit_Entry (U : Unit_Type; R : in out Unit_Rec);

      -----------------------
      -- Update_Unit_Entry --
      -----------------------

      procedure Update_Unit_Entry (U : Unit_Type; R : in out Unit_Rec) is
         pragma Unreferenced (U);
         use Subp_Maps;

         C        : Cursor;
         Inserted : Boolean;
      begin
         R.Subps.Insert (Subp, Default_Stat, C, Inserted);
         Process (R.Subps (C));
      end Update_Unit_Entry;

      use Unit_Maps;
      C        : Cursor;
      Inserted : Boolean;

      --  Start of processing for Update_Subp_Entry

   begin
      Unit_Map.Insert
        (Unit,
         Unit_Rec'
           (Analysis    => Progress_None,
            Stop_Reason => Stop_Reason_None,
            Subps       => Subp_Maps.Empty_Map),
         C,
         Inserted);
      Unit_Map.Update_Element (C, Update_Unit_Entry'Access);
   end Update_Subp_Entry;

end Report_Database;
