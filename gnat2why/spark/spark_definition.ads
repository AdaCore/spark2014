------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2013, AdaCore                     --
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

---------------------------------
-- Detection of SPARK Entities --
---------------------------------

--  All entities from the program are marked as being in SPARK or not in SPARK,
--  so that the translation to Why3 processes adequately the entity depending
--  on its status. The order of definition in Why3 follows the order in which
--  marking is applied to entities.

--  An error is issued if an entity which should be in SPARK, according to the
--  applicable SPARK_Mode pragma, is not in SPARK.

--  All entities declared locally to a toplevel subprogram body are either all
--  in SPARK, and listed for translation, or not listed for translation if a
--  violation was detected in the body.

with Types;          use Types;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

package SPARK_Definition is

   Entity_List : List_Of_Nodes.List;
   --  Lists of entities that should be translated to Why3. This list contains
   --  both entities in SPARK and entities not in SPARK. VCs should be
   --  generated only for entities in the current unit. Each entity may
   --  be attached to a declaration or not (for Itypes).

   Entity_Set : Node_Sets.Set;
   --  Set of all entities marked so far. This contains both entities from the
   --  current compiled unit, and entities from other units.

   procedure Before_Marking (Basename : String);
   --  Create a file to store detailed information about the SPARK status of
   --  toplevel subprograms (spec/body in SPARK or not). Use the argument as
   --  the base of the file.

   procedure After_Marking;
   --  Close the file created by Before_Marking.

   procedure Mark_Compilation_Unit (N : Node_Id);
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which it depends have been marked.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function Entity_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if entity E is in SPARK. Note that E may be in SPARK
   --  without being marked by the user in SPARK, in which case it can be
   --  called from SPARK code, but no VC will be generated for E.

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if the spec of subprogram or package E was marked in SPARK

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if the body of subprogram or package E was marked in SPARK

end SPARK_Definition;
