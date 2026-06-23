------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                     S P A R K _ J S O N _ E N T I T I E S                --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that it will be useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for more details.  You should have received a copy of the GNU     --
-- General Public License distributed with gnatprove; see file COPYING3. If --
-- not, go to http://www.gnu.org/licenses for a complete copy of the license.--
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Indefinite_Vectors;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with GNATCOLL.JSON; use GNATCOLL.JSON;

package SPARK_JSON_Entities is

   type Entity_Sloc is record
      File   : Unbounded_String;
      Line   : Positive;
      Column : Positive;
   end record;

   package Sloc_Vectors is new
     Ada.Containers.Indefinite_Vectors
       (Index_Type   => Positive,
        Element_Type => Entity_Sloc);

   type Entity_Info is record
      Key              : Unbounded_String;
      Name             : Unbounded_String;
      Sloc             : Sloc_Vectors.Vector;
      Manifest_Kind    : Unbounded_String;
      Manifest_Profile : Unbounded_String;
   end record;

   package Entity_Vectors is new
     Ada.Containers.Indefinite_Vectors
       (Index_Type   => Positive,
        Element_Type => Entity_Info);

   function Parse_Entity_Table
     (Table : JSON_Value) return Entity_Vectors.Vector;
   --  Parse a .spark "entities" table into records independent of any
   --  consumer's lookup state.

end SPARK_JSON_Entities;
