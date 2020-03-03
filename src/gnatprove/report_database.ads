------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
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

--  This package manages registering and querying the analysis results of
--  gnatprove.

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Assumptions;           use Assumptions;
with Assumption_Types;      use Assumption_Types;
with VC_Kinds;              use VC_Kinds;

package Report_Database is

   type Analysis_Status is
     (No_Analysis,      --  No analysis was performed on the unit
      Flow_Analysis,    --  Only flow analysis was performed on the unit
      Proof_Only,       --  Only proof was performed on the unit
      Flow_And_Proof);  --  Flow analysis and proof were performed on the unit

   type Suppressed_Warning is record
      Reason : Unbounded_String;
      File   : Unbounded_String;
      Line   : Integer;
      Column : Integer;
      --  ??? Line and Column are Positive (or at least Natural)
   end record;

   package Warning_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Suppressed_Warning, "=");

   --  Record of results obtained for a given subprogram or package
   type Stat_Rec is record
      SPARK           : Boolean;            --  In SPARK or not
      Analysis        : Analysis_Status;    --  Status of analysis performed
      Suppr_Msgs      : Warning_Lists.List; --  List of suppressed messages
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
      CodePeer  : Natural;
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

   Summary : Summary_Type := (others => Null_Summary_Line);

   type Flow_Message_Kind is (FMK_Error, FMK_Check, FMK_Warning);

   procedure Add_Flow_Result
     (Unit     : Unit_Type;
      Subp     : Subp_Type;
      Msg_Kind : Flow_Message_Kind);
   --  For the subprogram in the given unit, register a flow result, which is
   --  either a warning or an error.

   procedure Add_Proof_Result
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Proved : Boolean);
   --  For the subprogram in the given unit, register a proof result

   procedure Add_SPARK_Status
     (Unit         : Unit_Type;
      Subp         : Subp_Type;
      SPARK_Status : Boolean;
      Analysis     : Analysis_Status);
   --  Register the SPARK status as well as the level of analysis performed
   --  for the given unit.

   procedure Add_Suppressed_Warning
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Reason : String;
      File   : String;
      Line   : Integer;
      Column : Integer);
   --  For the subprogram in the given unit, register a suppressed warning with
   --  a reason.

   procedure Add_Claim_With_Assumptions (Claim : Token; S : Token_Sets.Set);
   --  Register that claim C ultimately only depends on assumptions S

   function Has_Unproved_Check return Boolean is
      (for some Check_Kind in Summary'Range =>
          Summary (Check_Kind).Unproved > 0);

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

   procedure Iter_Units
     (Process : not null access procedure (U : Unit_Type);
      Ordered : Boolean := False);
   --  Iterate over all units. If Ordered is True, iterate in a fixed order
   --  defined by the lexicographic order on unit names.

   procedure Iter_Unit_Subps
     (Unit    : Unit_Type;
      Process : not null access procedure (Subp : Subp_Type; Stat : Stat_Rec);
      Ordered : Boolean := False);
   --  Iterate over all subprograms of a given Unit. If Ordered is True,
   --  iterate in a fixed order defined by the lexicographic order on
   --  subprogram names.

   procedure Merge_Stat_Maps (A : in out Prover_Stat_Maps.Map;
                              B : Prover_Stat_Maps.Map);
   --  "Add" the second map of prover stats to the first, so that count and
   --  maximum values area taken into acount

end Report_Database;
