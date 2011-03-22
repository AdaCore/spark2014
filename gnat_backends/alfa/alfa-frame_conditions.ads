------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                A L F A . F R A M E _ C O N D I T I O N S                 --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Ada.Strings.Unbounded.Hash;

with ALFA.Common;                use ALFA.Common;

package ALFA.Frame_Conditions is

   function Nat_Hash (X : Nat) return Hash_Type is (Hash_Type (X));

   package Nat_To_String is new Hashed_Maps
     (Key_Type        => Nat,
      Element_Type    => Unbounded_String,
      Hash            => Nat_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package String_To_Nat is new Hashed_Maps
     (Key_Type        => Unbounded_String,
      Element_Type    => Nat,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   File_Names : Nat_To_String.Map;
   --  Mapping from file numbers to file names

   File_Nums  : String_To_Nat.Map;
   --  Mapping from file names to file numbers

   type Entity_Rep is record
      File : Nat;
      Line : Nat;
      Col  : Nat;
   end record;
   --  Representative of an entity

   Null_Entity : constant Entity_Rep := Entity_Rep'(File => 0,
                                                    Line => 0,
                                                    Col  => 0);

   function Rep_Hash (E : Entity_Rep) return Hash_Type is
     (Hash_Type (E.File * 53 + E.Line * 17 + E.Col));
   --  Hash function for hashed-maps

   package Rep_Set is new Hashed_Sets
     (Element_Type        => Entity_Rep,
      Hash                => Rep_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   use Rep_Set;

   package Rep_Map is new Hashed_Maps
     (Key_Type        => Entity_Rep,
      Element_Type    => Rep_Set.Set,
      Hash            => Rep_Hash,
      Equivalent_Keys => "=",
      "="             => Rep_Set."=");
   use Rep_Map;

   Defines : Rep_Map.Map;
   Params  : Rep_Map.Map;  --  only OUT and IN OUT parameters
   Writes  : Rep_Map.Map;
   Reads   : Rep_Map.Map;
   Callers : Rep_Map.Map;
   Calls   : Rep_Map.Map;

   procedure Add_To_Map (Map : in out Rep_Map.Map; From, To : Entity_Rep);
   --  Add the relation From -> To in map Map

   function Count_In_Map
     (Map : Rep_Map.Map;
      Ent : Entity_Rep) return Nat;
   --  Return the number of elements in the set associated to Ent in Map, or
   --  else 0.

   function Defines_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Params_Of (Ent : Entity_Rep) return Rep_Set.Set is
     (Params.Element (Ent));
   function Reads_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Global_Reads_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Writes_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Global_Writes_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Callers_Of (Ent : Entity_Rep) return Rep_Set.Set;
   function Calls_Of (Ent : Entity_Rep) return Rep_Set.Set;

   procedure Display_Maps;
   --  Send maps to output for debug

   procedure Load_ALFA (ALI_Filename : String);
   --  Extract xref information from an ALI file

   procedure Propagate_Through_Call_Graph;
   --  Propagate reads and writes through the call-graph defined by calls and
   --  callers.

   ----------------------------
   -- Link with AST Entities --
   ----------------------------

   use Id_Set;

   package Entity_Id_To_Rep is new Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Entity_Rep,
      Hash            => Id_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   use Entity_Id_To_Rep;

   From_AST : Entity_Id_To_Rep.Map;

   package Entity_Rep_To_Id is new Hashed_Maps
     (Key_Type        => Entity_Rep,
      Element_Type    => Entity_Id,
      Hash            => Rep_Hash,
      Equivalent_Keys => "=",
      "="             => "=");
   use Entity_Rep_To_Id;

   To_AST : Entity_Rep_To_Id.Map;

   procedure Declare_Entity (E : Entity_Id);
   --  Create a representative for E and enter the match in tables To_AST and
   --  From_AST.

   procedure Declare_All_Entities;
   --  Declare all entities by traversing all units

   procedure Get_Reads
     (E    : Entity_Id;
      Ids  : out Id_Set.Set;
      Reps : out Rep_Set.Set);
   --  Get the variables read by subprogram E, either as an Entity_Id in Ids if
   --  one is known, or as an Entity_Rep in Reps otherwise.

   procedure Get_Writes
     (E    : Entity_Id;
      Ids  : out Id_Set.Set;
      Reps : out Rep_Set.Set);
   --  Get the variables written by subprogram E, either as an Entity_Id in Ids
   --  if one is known, or as an Entity_Rep in Reps otherwise.

end ALFA.Frame_Conditions;
