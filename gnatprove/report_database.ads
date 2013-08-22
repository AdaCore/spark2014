------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                        R E P O R T _ D A T A B A S E                     --
--                                                                          --
--                                 S p e c                                  --
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

--  This package manages registering and querying the analysis results of
--  gnatprove.

with GNATCOLL.Symbols; use GNATCOLL.Symbols;

package Report_Database is

   type Unit_Type is private;

   type Subp_Type is private;

   type Stat_Rec is record
      VC_Count  : Integer;
      VC_Proved : Integer;
   end record;

   function Mk_Unit (Name : String) return Unit_Type;
   --  Build a unit from its name

   function Mk_Subp (Name : String; File : String; Line : Integer)
                     return Subp_Type;
   --  Build a a subp object from its defining components

   procedure Add_Proof_Result
     (Unit : Unit_Type; Subp : Subp_Type; Proved : Boolean);
   --  For the subprogram in the given unit, register a proof result

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

   procedure Iter_Units
     (Process : not null access procedure (U : Unit_Type));
   --  Iterate over all units

   procedure Iter_Unit_Subps
     (Unit : Unit_Type;
      Process : not null access procedure (Subp : Subp_Type; Stat : Stat_Rec));
   --  Iterate over all subprograms of a given Unit

private

   type Unit_Type is new Symbol;

   type Subp_Type_Rec is record
      Name : Symbol;
      File : Symbol;
      Line : Integer;
   end record;

   type Subp_Type is access constant Subp_Type_Rec;

end Report_Database;
