------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2012, AdaCore                     --
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

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

package Alfa.Definition is

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  Return whether aggregate N is fully initialized

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean;
   --  Return whether all aggregates in node N (recursively) are fully
   --  initialized.

   procedure Mark_Compilation_Unit (N : Node_Id);
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which it depends have been marked.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function Standard_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether standard entity Id is in Alfa or not

   procedure Create_Alfa_Output_File (Filename : String);
   --  Create the file in which to generate output about subprogram in/out of
   --  the Alfa subset.

   procedure Close_Alfa_Output_File;
   --  Close the file created by Create_Alfa_Output_File

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean;
   --  Given the entity E for a function, determine whether E is an expression
   --  function that only calls expression functions, directly or indirectly.

   function Body_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether the body of subprogram Id is in Alfa

   function Object_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether an object Id is in Alfa

   function Spec_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether the spec of subprogram Id is in Alfa

   function Type_Is_In_Alfa (Ent : Entity_Id) return Boolean;
   --  Return whether a type Ent is in Alfa. Contrary to other .._Is_In_Alfa
   --  functions, it takes an entity rather than a unique entity. Indeed,
   --  private types are always in Alfa, even when the corresponding full type
   --  is not in Alfa. This corresponds to cases where a client of the package,
   --  which has only view over the private declaration, may still be in Alfa,
   --  while an operation in the package over non-Alfa fields may not be in
   --  Alfa.

   type Alfa_Decl is
     (Alfa_Object,
      Alfa_Type,
      Non_Alfa_Object,  --  Entities, not declarations
      Non_Alfa_Type,    --  Entities, not declarations
      Alfa_Subprogram_Spec,
      Alfa_Subprogram_Body);

   Spec_Entities : List_Of_Nodes.List;
   Body_Entities : List_Of_Nodes.List;
   --  Lists of entities which are defined in the current unit, that require
   --  a translation in Why3. One is for entities defined in the spec, and the
   --  other for entities defined in the body. These lists contains both
   --  entities in Alfa and entities not in Alfa. Each entity may be
   --  attached to a declaration or not (for Itypes).

   All_Entities : Node_Sets.Set;
   --  Set of all entities in list Entities

end Alfa.Definition;
