------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      S P A R K _ D E F I N I T I O N                     --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2015, AdaCore                     --
--                     Copyright (C) 2014-2015, Altran UK Limited           --
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

with Ada.Containers.Hashed_Maps;
with Atree;             use Atree;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with GNATCOLL.JSON;     use GNATCOLL.JSON;
with Types;             use Types;

package SPARK_Definition is

   Entity_List : Node_Lists.List;
   --  List of entities that should be translated to Why3. This list contains
   --  both entities in SPARK and entities not in SPARK. VCs should be
   --  generated only for entities in the current unit. Each entity may
   --  be attached to a declaration or not (for Itypes).

   Entity_Set : Node_Sets.Set;
   --  Set of all entities marked so far. It contains entities from both the
   --  current compilation unit and other units.

   type Instance_Number is (One, Many);

   package Task_Instances_Maps is
     new Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                     Element_Type    => Instance_Number,
                                     Hash            => Name_Hash,
                                     Equivalent_Keys => "=");
   --  Containers that map tasks to number of their instances

   Task_Instances : Task_Instances_Maps.Map;
   --  Task instances

   Max_Array_Dimensions : constant Positive := 4;
   --  Maximal number of array dimensions that are currently supported

   Emit_Messages : Boolean := True;
   --  Emit messages only if this is set. We do not want to produce any
   --  error messages during marking when we generate globals (only the
   --  marking itself is important).

   procedure Mark_Compilation_Unit (N : Node_Id);
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which it depends have been marked.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function Entity_Marked (E : Entity_Id) return Boolean;
   --  Returns True if entity E has already been considered for marking.

   function Entity_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if entity E is in SPARK. Note that E may be in SPARK
   --  without being marked by the user in SPARK, in which case it can be
   --  called from SPARK code, but no VC will be generated for E.
   --
   --  Further note for subprograms this only works for the specification.
   --  To check if a subprogram's body is in SPARK and contains no SPARK
   --  violations use Entity_Body_Valid_SPARK.

   function Entity_Spec_In_SPARK (E : Entity_Id) return Boolean;
   --  @param E a subprogram, package or task entity
   --  @return True if the spec of E was marked in SPARK. Note this does not
   --    mean that the subprogram is valid SPARK, only that SPARK_Mode is On.

   function Entity_Body_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if the body of subprogram or package E was marked in
   --  SPARK. Note this does not mean that the subprogram is valid SPARK,
   --  only that SPARK_Mode is On.

   function Entity_Body_Valid_SPARK (E : Entity_Id) return Boolean
     with Pre => Ekind (E) in Subprogram_Kind | E_Task_Type | E_Entry
                 and then Entity_Body_In_SPARK (E);
   --  Returns True if the given entitys' body contains no SPARK violations

   function Full_View_Not_In_SPARK (E : Entity_Id) return Boolean;
   --  Returns True if the underlying type of the type E is not in SPARK,
   --  declared in a private part with SPARK_Mode => Off or in a private part
   --  of a package with external axioms. Also returns True if E is a subtype
   --  or derived type of such an entity.

   function Get_First_Ancestor_In_SPARK (E : Entity_Id) return Entity_Id with
     Pre  => Full_View_Not_In_SPARK (E),
     Post => Entity_In_SPARK (Get_First_Ancestor_In_SPARK'Result);
   --  Returns the first type in SPARK in the ancestors of E.

   function Get_SPARK_JSON return JSON_Array;
   --  Should be called after marking is finished. Returns the result of
   --  marking as a JSON record.

   function Is_Actions_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff entity E is defined in actions and thus requires a
   --  special translation. See gnat2why.ads for details.

   function Is_Loop_Entity (E : Entity_Id) return Boolean;
   --  Returns True iff entity E is defined in loop before the invariants and
   --  thus may require a special translation. See gnat2why.ads for details.

end SPARK_Definition;
