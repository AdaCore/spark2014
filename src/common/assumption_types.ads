------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                         A S S U M P T I O N _ T Y P E S                  --
--                                                                          --
--                                  S p e c                                 --
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
with Ada.Containers.Doubly_Linked_Lists;
with GNATCOLL.JSON;                      use GNATCOLL.JSON;
with GNATCOLL.Symbols;                   use GNATCOLL.Symbols;

package Assumption_Types is

   type Subp_Type is private;
   type Unit_Type is private;

   type Base_Sloc is record
      File : Symbol;
      Line : Integer;
   end record;

   function Base_Sloc_File (Subp : Base_Sloc) return String;

   package Sloc_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Base_Sloc,
      "="          => "=");

   subtype My_Sloc is Sloc_Lists.List;
   --  The type of slocs used in assumptions and more generally in the report
   --  file.

   function Subp_Name (Subp : Subp_Type) return String;
   function Subp_Sloc (Subp : Subp_Type) return My_Sloc;

   function From_JSON (V : JSON_Value) return Subp_Type;
   function To_JSON (S : Subp_Type) return JSON_Value;

   function Mk_Base_Sloc (File : String; Line : Positive) return Base_Sloc;
   function Mk_Subp (Name : String; Sloc : My_Sloc) return Subp_Type;
   --  Build a subp object from its defining components

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
      Sloc : My_Sloc;
   end record;

   type Subp_Type is not null access constant Subp_Type_Rec;

end Assumption_Types;
