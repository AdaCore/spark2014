------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

--  This package manages registering and querying the analysis results of
--  gnatprove.

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Assumptions;           use Assumptions;
with Assumption_Types;      use Assumption_Types;
with VC_Kinds;              use VC_Kinds;

package Report_Database is

   type Suppressed_Check is record
      Justif_Msg : Unbounded_String;
      Kind       : Unbounded_String;
      Reason     : Unbounded_String;
      File       : Unbounded_String;
      Line       : Positive;
      Column     : Positive;
   end record;

   type Pragma_Assume is record
      File   : Unbounded_String;
      Line   : Positive;
      Column : Positive;
      Subp   : Subp_Type;
   end record;

   package Check_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Suppressed_Check, "=");

   package Pragma_Assume_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Pragma_Assume, "=");

   --  Record of results obtained for a given subprogram or package
   type Stat_Rec is record
      SPARK           : SPARK_Mode_Status;  --  SPARK On, only Spec, or Off
      Suppr_Checks    : Check_Lists.List;   --  List of suppressed checks
      Pragma_Assumes  : Pragma_Assume_Lists.List; -- List of pragma Assumes
      Flow_Warnings   : Natural;            --  Number of flow analysis warning
      Flow_Errors     : Natural;            --  Number of flow analysis errors
      Flow_Checks     : Natural;            --  Number of flow analysis checks
      Proof_Warnings  : Natural;            --  Number of proof warnings
      Proof_Checks    : Natural;            --  Total number of checks
      Proof_Checks_OK : Natural;            --  Number of checks proved
      Assumptions     : Rule_Lists.List;    --  Final mapping claim->assumption
   end record;

   type All_Prover_Stat is record
      Total   : Natural;
      Provers : Prover_Stat_Maps.Map;
   end record;

   type Summary_Line is record
      Flow      : Natural;
      Provers   : All_Prover_Stat;
      Justified : Natural;
      Unproved  : Natural;
   end record;

   type Possible_Entries is
     (No_Entry,
      Warnings,
      Data_Dep,
      Flow_Dep,
      Init,
      Non_Aliasing,
      Runtime_Checks,
      Assertions,
      Functional_Contracts,
      LSP,
      Termination,
      Concurrency,
      Total);
   pragma Ordered (Possible_Entries);

   subtype Summary_Entries is Possible_Entries range Data_Dep .. Total;

   type Summary_Type is array (Summary_Entries) of Summary_Line;

   Empty_Prover_Stats : constant All_Prover_Stat :=
     (Total => 0, Provers => Prover_Stat_Maps.Empty_Map);

   Null_Summary_Line : constant Summary_Line :=
     (Provers => Empty_Prover_Stats, others => 0);

   Summary : Summary_Type := [others => Null_Summary_Line];

   type Flow_Message_Kind is (FMK_Error, FMK_Check, FMK_Warning);

   procedure Add_Flow_Result
     (Unit     : Unit_Type;
      Subp     : Subp_Type;
      Msg_Kind : Flow_Message_Kind);
   --  For the subprogram in the given unit, register a flow result, which is
   --  either a warning or an error.

   procedure Add_Pragma_Assume_Result
     (Unit   : Unit_Type;
      File   : String;
      Line   : Positive;
      Column : Positive;
      Subp   : Subp_Type);
   --  For the subprogram in the given unit, register a pragma assume result

   procedure Add_Proof_Result
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Proved : Boolean);
   --  For the subprogram in the given unit, register a proof result

   procedure Add_SPARK_Status
     (Unit         : Unit_Type;
      Subp         : Subp_Type;
      SPARK_Status : SPARK_Mode_Status);
   --  Register the SPARK status for the given subprogram

   procedure Add_Analysis_Progress
     (Unit        : Unit_Type;
      Progress    : Analysis_Progress;
      Stop_Reason : Stop_Reason_Type);

   procedure Add_Suppressed_Check
     (Unit       : Unit_Type;
      Subp       : Subp_Type;
      Justif_Msg : String;
      Kind       : String;
      Reason     : String;
      File       : String;
      Line       : Positive;
      Column     : Positive);
   --  For the subprogram in the given unit, register a suppressed check with a
   --  reason.

   procedure Add_Claim_With_Assumptions (Claim : Token; S : Token_Sets.Set);
   --  Register that claim C ultimately only depends on assumptions S

   function Has_Unproved_Check return Boolean is
      (for some Check_Kind in Summary'Range =>
          Summary (Check_Kind).Unproved > 0);

   procedure Add_Skip_Proof (S : Subp_Type);
   --  Register that proofs were skipped for S

   function Has_Skip_Proof (S : Subp_Type) return Boolean;
   --  Check whether proofs were skipped for S

   procedure Reset_All_Results;
   --  Resets the results, removing all information on units and subprograms

   procedure Iter_All_Subps
     (Process : not null access
                   procedure (U : Unit_Type;
                              Subp : Subp_Type;
                              Stat : Stat_Rec));
   --  Iterate over all subprograms of all units

   function Num_Units return Natural;
   --  Return the number of units

   function Num_Subps (Unit : Unit_Type) return Natural;
   --  Return the number of subprograms in the unit

   function Num_Subps_SPARK (Unit : Unit_Type) return Natural;
   --  Return the number of subprograms in SPARK in the unit

   function Unit_Progress (Unit : Unit_Type) return Analysis_Progress;
   --  Return the progress status for the unit

   function Unit_Stop_Reason (Unit : Unit_Type) return Stop_Reason_Type;
   --  Return the reason the analysis stopped for this unit

   procedure Iter_Units
     (Process : not null access procedure (U : Unit_Type);
      Ordered : Boolean := False);
   --  Iterate over all units. If Ordered is True, iterate in a fixed order
   --  defined by the lexicographic order on unit names.

   procedure Iter_Unit_Subps
     (Unit    : Unit_Type;
      Process : not null access procedure (Subp : Subp_Type;
                                           Stat : Stat_Rec;
                                           Progress : Analysis_Progress);
      Ordered : Boolean := False);
   --  Iterate over all subprograms of a given Unit. If Ordered is True,
   --  iterate in a fixed order defined by the lexicographic order on
   --  subprogram names.

   procedure Merge_Stat_Maps (A : in out Prover_Stat_Maps.Map;
                              B : Prover_Stat_Maps.Map);
   --  "Add" the second map of prover stats to the first, so that count and
   --  maximum values area taken into acount

end Report_Database;
