------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                      Copyright (C) 2011-2013, AdaCore                    --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

--  Compute the frame condition of all subprograms in the current call-graph,
--  by propagating reads and writes from callees to callers. Externally,
--  entities (whether subprograms or variables) are represented as strings,
--  which may or may not correspond to entities in the AST, as some variables
--  and subprograms are not visible from the current compilation unit.
--  Internally, entities are represented as integers, to avoid costly repeated
--  hashing of strings in computations over sets/maps of entities.

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Strings.Hash;

with Types;                      use Types;

package SPARK_Frame_Conditions is

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

   package Name_Map is new Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Entity_Name,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => Name_Equal);
   use Name_Map;

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean;
   --  Return whether Ent is the special variable "__HEAP"

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

   function File_Of_Entity (E : Entity_Name) return Entity_Name;
   --  Return the name of the file defining the entity E

   procedure Load_SPARK_Xrefs (ALI_Filename : String);
   --  Extract xref information from an ALI file

   procedure Set_Ignore_Errors (Ignore_Errors : Boolean);
   --  Set a flag to ignore failures to find some scope that should have been
   --  present in some ALI file.

   procedure Propagate_Through_Call_Graph (Ignore_Errors : Boolean);
   --  Propagate reads and writes through the call-graph defined by calls and
   --  callers. If Ignore_Errors is true, then ignore failures to find some
   --  scope that should have been present in some ALI file. This mode is used
   --  in simpler modes of operation that do not lead to translation into Why.

   --  -----------------------------------------
   --  Mapping between Entities and Entity_Names
   --  -----------------------------------------

   --  The following two procedures are used to fill in and query a map that
   --  stores the entity (if present) for a given entity_name. Basically, if
   --  the entity name is present somewhere in the closure of the with'ed specs
   --  of the current unit, then Find_Object_Entity will return it.

   procedure Register_Object_Entity (E : Entity_Id);
   --  Register the object entity

   function Find_Object_Entity (E : Entity_Name) return Entity_Id;
   --  Find the entity that belongs to the given Entity_Name. If no such entity
   --  could be found (i.e. when the object is defined in the body of a with'ed
   --  unit), the empty node is returned.

end SPARK_Frame_Conditions;
