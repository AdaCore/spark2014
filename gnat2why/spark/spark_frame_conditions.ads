------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                S P A R K _ F R A M E _ C O N D I T I O N S               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2011-2020, AdaCore                     --
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

with Atree;             use Atree;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Types;             use Types;

package SPARK_Frame_Conditions is

   function Is_Heap_Variable (Ent : Entity_Name) return Boolean;
   --  Return True iff Ent is the special variable "__HEAP"

   function Is_Heap_Variable (E : Entity_Id) return Boolean
   with Pre => Present (E);
   --  Return True iff E is the special variable "__HEAP"

   procedure Display_Maps;
   --  Send maps to output for debug

   function Computed_Calls (E : Entity_Id) return Node_Sets.Set;
   --  Get subprograms directly called by subprogram E

   procedure Load_SPARK_Xrefs;
   --  Extract xref information from low-level data structures

   procedure Collect_Direct_Computed_Globals
     (E       :     Entity_Id;
      Inputs  : out Node_Sets.Set;
      Outputs : out Node_Sets.Set)
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

end SPARK_Frame_Conditions;
