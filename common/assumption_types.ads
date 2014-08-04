------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                         A S S U M P T I O N _ T Y P E S                  --
--                                                                          --
--                                  S p e c                                 --
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

with Ada.Containers;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with GNATCOLL.Symbols;      use GNATCOLL.Symbols;

package Assumption_Types is

   type Subp_Type is private;
   type Unit_Type is private;

   Null_Subp : constant Subp_Type;

   function Subp_Name (Subp : Subp_Type) return String;
   function Subp_File (Subp : Subp_Type) return String;
   function Subp_Line (Subp : Subp_Type) return Integer;

   function From_JSON (V : JSON_Value) return Subp_Type;
   function To_JSON (S : Subp_Type) return JSON_Value;

   function Mk_Subp (Name : String; File : String; Line : Integer)
                     return Subp_Type;
   --  Build a a subp object from its defining components

   function Mk_Unit (Name : String) return Unit_Type;
   --  Build a unit from its name

   function Unit_Name (Unit : Unit_Type) return String;

   function Hash (S : Subp_Type) return Ada.Containers.Hash_Type;
   function Hash (S : Unit_Type) return Ada.Containers.Hash_Type;

   function "<" (Left, Right : Subp_Type) return Boolean;
   function "<" (Left, Right : Unit_Type) return Boolean;

private

   type Unit_Type is new Symbol;

   type Subp_Type_Rec is record
      Name : Symbol;
      File : Symbol;
      Line : Integer;
   end record;

   type Subp_Type is access constant Subp_Type_Rec;

   Null_Subp : constant Subp_Type := null;

end Assumption_Types;
