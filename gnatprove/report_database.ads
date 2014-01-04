------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with GNATCOLL.Symbols;      use GNATCOLL.Symbols;

package Report_Database is

   type Unit_Type is private;

   type Subp_Type is private;

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
   end record;

   function Mk_Unit (Name : String) return Unit_Type;
   --  Build a unit from its name

   function Mk_Subp (Name : String; File : String; Line : Integer)
                     return Subp_Type;
   --  Build a a subp object from its defining components

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

   procedure Reset_All_Results;
   --  Resets the results, removing all information on units and subprograms

   procedure Iter_All_Subps
     (Process : not null access
                   procedure (U : Unit_Type;
                              Subp : Subp_Type;
                              Stat : Stat_Rec));
   --  Iterate over all subprograms of all units

   function Unit_Name (Unit : Unit_Type) return String;

   function Subp_Name (Subp : Subp_Type) return String;
   function Subp_File (Subp : Subp_Type) return String;
   function Subp_Line (Subp : Subp_Type) return Integer;

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

private

   type Unit_Type is new Symbol;

   type Subp_Type_Rec is record
      Name : Symbol;
      File : Symbol;
      Line : Integer;
   end record;

   type Subp_Type is access constant Subp_Type_Rec;

end Report_Database;
