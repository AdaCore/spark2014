------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                      Copyright (C) 2011-2017, AdaCore                    --
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
with Ada.Containers.Hashed_Sets;
with ALI;                             use ALI;
with Atree;                      use Atree;
with Common_Containers;          use Common_Containers;
with Einfo;                      use Einfo;
with Namet;                      use Namet;
with Types;                      use Types;

package SPARK_Frame_Conditions is

   use Name_Sets;

   Translated_Object_Entities : Name_Sets.Set := Name_Sets.Empty_Set;
   --  Filled by gnat2why-driver.adb, and represents all object entities that
   --  are actually translated to Why.

   function File_Name_Hash (F : File_Name_Type) return Hash_Type is
     (Hash_Type (F));

   package File_Name_Set is new Hashed_Sets
     (Element_Type        => File_Name_Type,
      Hash                => File_Name_Hash,
      Equivalent_Elements => "=",
      "="                 => "=");
   use File_Name_Set;

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean;
   --  Return True iff Ent is the special variable "__HEAP"

   procedure Display_Maps;
   --  Send maps to output for debug

   function Computed_Calls (E_Name : Entity_Name) return Name_Sets.Set;
   --  Get subprograms directly called by subprogram E_Name

   function Computed_Reads (E : Entity_Id) return Name_Sets.Set
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure
                          | E_Task_Type;
   --  Get the variables read by subprogram E. If Include_Constants is True
   --  then include constants in the result (for flow analysis); if it is
   --  False then do not (for proof).

   function Computed_Writes (E : Entity_Id) return Name_Sets.Set
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Procedure
                          | E_Task_Type;
   --  Get the variables written by subprogram E

   function File_Of_Entity (E : Entity_Name) return Entity_Name;
   --  Return the name of the file defining the entity E

   procedure Load_SPARK_Xrefs (ALI_File : ALI_Id);
   --  Extract xref information from an ALI file

   procedure Collect_Direct_Computed_Globals
     (E       :     Entity_Id;
      Inputs  : out Name_Sets.Set;
      Outputs : out Name_Sets.Set)
   with Pre  => Ekind (E) in Entry_Kind
                           | E_Function
                           | E_Procedure
                           | E_Task_Type,
        Post => Outputs.Is_Subset (Of_Set => Inputs);
   --  Collect the Computed Globals information based on the current
   --  compilation unit alone.
   --
   --  This procedure is only called in phase 1 so no ALI file is actually
   --  read; it creates flow analysis' Generated Globals when a subprogram is
   --  NOT in SPARK.
   --
   --  The Inputs set will contain both variables that are either read or
   --  written (since the Computed Globals are an over-approximation).

   procedure Propagate_Through_Call_Graph;
   --  Propagate reads and writes through the call-graph defined by calls and
   --  callers.
   --  ??? This procedure only initializes maps and doesn't propagate anything;
   --  the name comes from the the previous design of the generated globals.

   function Is_Protected_Operation (E_Name : Entity_Name) return Boolean;
   --  Return True if E_Name refers to entry or protected subprogram

   --  -----------------------------------------
   --  Mapping between Entities and Entity_Names
   --  -----------------------------------------

   --  The following two procedures are used to fill in and query a map that
   --  stores the entity (if present) for a given entity_name. Basically, if
   --  the entity name is present somewhere in the closure of the with'ed specs
   --  of the current compilation unit, then Find_Entity will return it.

   procedure Register_Entity (E : Entity_Id);
   --  Register the entity

   function Find_Entity (E : Entity_Name) return Entity_Id;
   --  Find the entity that belongs to the given Entity_Name. If no such entity
   --  could be found (i.e. when the entity is defined in the body of a with'ed
   --  unit), the empty node is returned.

   procedure For_All_External_Objects
     (Process : not null access procedure (E : Entity_Name));
   --  Invoke the callback for all object entity_names that do not correspond
   --  to an entity in the tree (i.e. are defined in some other unit body).

   procedure For_All_External_States
     (Process : not null access procedure (E : Entity_Name));
   --  Invoke the callback for all state entity_names that do not correspond to
   --  a state abstraction in the tree (i.e. are defined in some other unit
   --  body).

end SPARK_Frame_Conditions;
