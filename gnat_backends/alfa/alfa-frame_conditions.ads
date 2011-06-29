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
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Hash;

package Alfa.Frame_Conditions is

   type Entity_Name is new String_Ptr;
   --  Unique name representing an entity

   function Name_Equal (Left, Right : Entity_Name) return Boolean is
      (Left.all = Right.all);

   Null_Entity_Name : constant Entity_Name := null;

   function Name_Hash (E : Entity_Name) return Hash_Type is
      (Ada.Strings.Hash (E.all));

   package Name_Set is new Hashed_Sets
     (Element_Type        => Entity_Name,
      Hash                => Name_Hash,
      Equivalent_Elements => Name_Equal,
      "="                 => Name_Equal);
   use Name_Set;

   procedure Display_Maps;
   --  Send maps to output for debug

   function Get_Reads (E : Entity_Id) return Name_Set.Set;
   --  Get the variables read by subprogram E

   function Get_Writes (E : Entity_Id) return Name_Set.Set;
   --  Get the variables written by subprogram E

   function Has_Global_Reads (E : Entity_Id) return Boolean is
     (not Get_Reads (E).Is_Empty);
   --  Return True if subprogram E reads to global variables

   function Has_Global_Writes (E : Entity_Id) return Boolean is
     (not Get_Writes (E).Is_Empty);
   --  Return True if subprogram E writes to global variables

   procedure Load_Alfa (ALI_Filename : String);
   --  Extract xref information from an ALI file

   procedure Propagate_Through_Call_Graph (Ignore_Errors : Boolean);
   --  Propagate reads and writes through the call-graph defined by calls and
   --  callers. If Ignore_Errors is true, then ignore failures to find some
   --  scope that should have been present in some ALI file. This mode is used
   --  in simpler modes of operation that do not lead to translation into Why.

end Alfa.Frame_Conditions;
