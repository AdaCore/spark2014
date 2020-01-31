------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
with Ada.Containers.Ordered_Sets;

package body Report_Database is

   package Subp_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Subp_Type,
        Element_Type    => Stat_Rec,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Default_Stat : constant Stat_Rec :=
     Stat_Rec'(SPARK           => False,
               Analysis        => No_Analysis,
               Suppr_Msgs      => Warning_Lists.Empty_List,
               Flow_Warnings   => 0,
               Flow_Errors     => 0,
               Flow_Checks     => 0,
               Proof_Warnings  => 0,
               Proof_Checks    => 0,
               Proof_Checks_OK => 0,
               Assumptions     => Rule_Lists.Empty_List);

   package Ordered_Subp_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Subp_Type,
                                  "<"          => "<");

   package Unit_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Unit_Type,
        Element_Type    => Subp_Maps.Map,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => Subp_Maps."=");

   package Subp_Unit_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Subp_Type,
        Element_Type    => Unit_Type,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   package Ordered_Unit_Sets is new
     Ada.Containers.Ordered_Sets (Element_Type => Unit_Type,
                                  "<"          => "<");

   Unit_Map : Unit_Maps.Map := Unit_Maps.Empty_Map;

   Subp_Unit_Map : Subp_Unit_Maps.Map := Subp_Unit_Maps.Empty_Map;
   --  This map maps subprograms to their unit. It is filled by the
   --  Add_SPARK_Status procedure.

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec));
   --  Update the stat record of the given subp using the callback. If the
   --  unit/subp do not exist yet, add them and initialize to default Stat_Rec.

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
      Update_Subp_Entry (Subp_Unit_Map (Subp),
                         Subp,
                         Add_Claim_Entry'Access);
   end Add_Claim_With_Assumptions;

   ---------------------
   -- Add_Flow_Result --
   ---------------------

   procedure Add_Flow_Result
     (Unit     : Unit_Type;
      Subp     : Subp_Type;
      Msg_Kind : Flow_Message_Kind)
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

   ----------------------
   -- Add_Proof_Result --
   ----------------------

   procedure Add_Proof_Result
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Proved : Boolean)
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

   ----------------------
   -- Add_SPARK_Status --
   ----------------------

   procedure Add_SPARK_Status
     (Unit         : Unit_Type;
      Subp         : Subp_Type;
      SPARK_Status : Boolean;
      Analysis     : Analysis_Status) is

      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.SPARK := SPARK_Status;
         Stat.Analysis := Analysis;
      end Process;

   --  Start of processing for Add_SPARK_Status

   begin
      --  ??? We need to use include instead of insert because GNATprove
      --  currently mixes up packages and subprograms-acting-as packages

      Subp_Unit_Map.Include (Subp, Unit);
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_SPARK_Status;

   ----------------------------
   -- Add_Suppressed_Warning --
   ----------------------------

   procedure Add_Suppressed_Warning
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Reason : String;
      File   : String;
      Line   : Integer;
      Column : Integer)
   is
      procedure Process (Stat : in out Stat_Rec);
      --  Do the actual work

      -------------
      -- Process --
      -------------

      procedure Process (Stat : in out Stat_Rec) is
      begin
         Stat.Suppr_Msgs.Append
           (Suppressed_Warning'(Reason => To_Unbounded_String (Reason),
                                File   => To_Unbounded_String (File),
                                Line   => Line,
                                Column => Column));
      end Process;

   --  Start of processing for Add_Suppressed_Warning

   begin
      Update_Subp_Entry (Unit, Subp, Process'Access);
   end Add_Suppressed_Warning;

   --------------------
   -- Iter_All_Subps --
   --------------------

   procedure Iter_All_Subps
     (Process : not null access
                   procedure (U : Unit_Type;
                              Subp : Subp_Type;
                              Stat : Stat_Rec))
   is
   begin
      for Unit_C in Unit_Map.Iterate loop
         for Subp_C in Unit_Map (Unit_C).Iterate loop
            Process (Unit_Maps.Key (Unit_C),
                     Subp_Maps.Key (Subp_C),
                     Unit_Map (Unit_C) (Subp_C));
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
      Process : not null access procedure (Subp : Subp_Type; Stat : Stat_Rec);
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
               for Subp_C in Unit_Map (C).Iterate loop
                  Names.Insert (Subp_Maps.Key (Subp_C));
               end loop;

               for Subp of Names loop
                  Process (Subp, Unit_Map (C) (Subp));
               end loop;
            end;

         --  Otherwise, directly iterate over map of units

         else
            for Subp_C in Unit_Map (C).Iterate loop
               Process (Subp_Maps.Key (Subp_C), Unit_Map (C) (Subp_C));
            end loop;
         end if;
      end if;
   end Iter_Unit_Subps;

   ---------------------
   -- Merge_Stat_Maps --
   ---------------------

   procedure Merge_Stat_Maps (A : in out Prover_Stat_Maps.Map;
                              B : Prover_Stat_Maps.Map) is

      procedure Merge_Stat (A : in out Prover_Stat;
                            B : Prover_Stat);

      ----------------
      -- Merge_Stat --
      ----------------

      procedure Merge_Stat (A : in out Prover_Stat;
                            B : Prover_Stat) is
      begin
         A := (Count     => A.Count + B.Count,
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
            A.Insert (Key      => Key (C),
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

   function Num_Subps (Unit : Unit_Type) return Natural is
     (Natural (Unit_Map (Unit).Length));

   ---------------------
   -- Num_Subps_SPARK --
   ---------------------

   function Num_Subps_SPARK (Unit : Unit_Type) return Natural
   is
      Count : Natural := 0;

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec);

      ------------
      -- Update --
      ------------

      procedure Update (Subp : Subp_Type; Stat : Stat_Rec) is
         pragma Unreferenced (Subp);
      begin
         if Stat.SPARK then
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

   function Num_Units return Natural is
     (Natural (Unit_Map.Length));

   -----------------------
   -- Reset_All_Results --
   -----------------------

   procedure Reset_All_Results is
   begin
      Unit_Map.Clear;
   end Reset_All_Results;

   -----------------------
   -- Update_Subp_Entry --
   -----------------------

   procedure Update_Subp_Entry
     (Unit    : Unit_Type;
      Subp    : Subp_Type;
      Process : not null access procedure (Stat : in out Stat_Rec))
   is
      procedure Update_Unit_Entry (U : Unit_Type; Map : in out Subp_Maps.Map);

      -----------------------
      -- Update_Unit_Entry --
      -----------------------

      procedure Update_Unit_Entry (U : Unit_Type; Map : in out Subp_Maps.Map)
      is
         pragma Unreferenced (U);
         use Subp_Maps;

         C        : Cursor;
         Inserted : Boolean;
      begin
         Map.Insert (Subp, Default_Stat, C, Inserted);
         Process (Map (C));
      end Update_Unit_Entry;

      use Unit_Maps;
      C        : Cursor;
      Inserted : Boolean;

   --  Start of processing for Update_Subp_Entry

   begin
      Unit_Map.Insert (Unit, Subp_Maps.Empty_Map, C, Inserted);
      Unit_Map.Update_Element (C, Update_Unit_Entry'Access);
   end Update_Subp_Entry;

end Report_Database;
