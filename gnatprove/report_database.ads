------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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
with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Assumptions;           use Assumptions;
with Assumption_Types;      use Assumption_Types;

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
   end record;

   package Warning_Lists is new
     Ada.Containers.Doubly_Linked_Lists (Suppressed_Warning, "=");

   --  Record of results obtained for a given subprogram or package
   type Stat_Rec is record
      SPARK         : Boolean;            --  In SPARK or not
      Analysis      : Analysis_Status;    --  Status of analysis performed
      Suppr_Msgs    : Warning_Lists.List; --  list of suppressed messages
      Flow_Warnings : Natural;            --  Number of flow analysis warnings
      Flow_Errors   : Natural;            --  Number of flow analysis errors
      VC_Count      : Natural;            --  Total number of checks
      VC_Proved     : Natural;            --  Number of checks that were proved
      Assumptions   : Rule_Lists.List;    --  final mapping claims->assumptions
   end record;

   package String_Maps is new Ada.Containers.Indefinite_Hashed_Maps
     (Key_Type        => String,
      Element_Type    => Natural,
      Hash            => Ada.Strings.Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   type Prover_Stat is record
      Total : Natural;
      Provers : String_Maps.Map;
   end record;

   type Summary_Line is record
      Flow : Natural;
      Interval : Natural;
      Provers : Prover_Stat;
      Justified : Natural;
      Unproved : Natural;
   end record;

   type Possible_Entries is
     (No_Entry,
      Data_Dep,
      Flow_Dep,
      Init,
      Non_Aliasing,
      Runtime_Checks,
      Assertions,
      Functional_Contracts,
      LSP);

   subtype Summary_Entries is Possible_Entries range Data_Dep .. LSP;

   type Summary_Type is array (Summary_Entries) of Summary_Line;

   Empty_Prover_Stats : Prover_Stat :=
     (Total => 0, Provers => String_Maps.Empty_Map);
   Null_Summary_Line : Summary_Line :=
     (Provers => Empty_Prover_Stats, others => 0);
   Summary : Summary_Type := (others => Null_Summary_Line);

   procedure Add_Flow_Result
     (Unit  : Unit_Type;
      Subp  : Subp_Type;
      Error : Boolean);
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
   --  Registers the SPARK status as well as the level of analysis performed
   --  for the given unit.

   procedure Add_Suppressed_Warning
     (Unit   : Unit_Type;
      Subp   : Subp_Type;
      Reason : String;
      File   : String;
      Line   : Integer;
      Column : Integer);
   --  For the subprogram in the given unit, register a suppressed warning with
   --  a reason

   procedure Add_Claim_With_Assumptions (Claim : Token; S : Token_Sets.Set);
   --  register that claim C ultimately only depends on assumptions S

   procedure Reset_All_Results;
   --  Resets the results, removing all information on units and subprograms

   procedure Iter_All_Subps
     (Process : not null access
                   procedure (U : Unit_Type;
                              Subp : Subp_Type;
                              Stat : Stat_Rec));
   --  Iterate over all subprograms of all units

   function Num_Units return Integer;
   --  Return the number of units

   function Num_Subps (Unit : Unit_Type) return Integer;
   --  return the number of subprograms in the unit

   function Num_Subps_SPARK (Unit : Unit_Type) return Integer;
   --  return the number of subprograms in SPARK in the unit

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

end Report_Database;
