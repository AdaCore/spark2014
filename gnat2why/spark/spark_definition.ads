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

--------------------------------
-- Detection of Alfa entities --
--------------------------------

--  All entities from the program are marked as being in Alfa or not in Alfa,
--  so that the translation to Why3 processes adequately the entity depending
--  on its status. The order of definition in Why3 follows the order in which
--  marking is applied to entities.

--  All entities except types are marked at the point where they are declared.
--  Forward references to an entity (such as a call to a subprogram in a
--  contract before this subprogram is declared) are not in Alfa. Types are
--  treated differently for two reasons:
--    * Itypes (implicit types introduced by the frontend) and class-wide types
--      may not have an explicit declaration, or one that is not attached to
--      the AST.
--    * Type definitions may refer to private types whose full view has not
--      been declared yet. It is this full view declaration which is translated
--      into Why3 when the type is in Alfa.
--  Therefore, to avoid forward references to types not yet defined in Why3:
--    * Itypes and class-wide types are marked the first time they are
--      referenced.
--    * All necessary types for a type definition (e.g. components of a record
--      type) are marked before the type itself.

--  Marking of an entity works as follows:
--    * A scope for the entity is pushed on a stack, and the definition of the
--      entity is marked. Any violation of Alfa during marking is recorded as
--      a violation for all entities on the stack. For example, the use of a
--      feature not in Alfa in the body of a local subprogram results in the
--      violation being attached to both subprograms.
--    * After marking, if no violation is attached to the entity, it is marked
--      as in Alfa. In any case, it is marked as being treated from now on, so
--      that future references are not counted as forward references.
--    * If the entity is defined in the spec or the body of the current
--      compiled unit, it is added to one of the list of entities Spec_Entities
--      or Body_Entities, which will be translated to Why3. The translation
--      will depend on the status (in Alfa or not) of each entity.

--  Subprogram specs and subprogram bodies are treated as two different scopes,
--  so that a subprogram spec can be in Alfa even if its body is not in Alfa.

--  Except for private types and deferred constants, a unique entity is used
--  for multiple views of the same entity. For example, the entity attached to
--  a subprogram body or a body stub is not used.

--  Private types are always in Alfa (except currently record (sub)type with
--  private part), even if the underlying type is not in Alfa. This allows
--  operations which do not depend on the underlying type to be in Alfa, which
--  is the case in client code that does not have access to the underlying
--  type. Since only the partial view of a private type is used in the AST
--  (except at the point of declaration of the full view), even when visibility
--  over the full view is needed, the nodes that need this full view are
--  treated specially, so that they are in Alfa only if the most underlying
--  type is in Alfa. This most underlying type is the last type obtained by
--  taking:
--  . for a private type, its underlying type
--  . for a record subtype, its base type
--  . for all other types, itself
--  until reaching a non-private type that is not a record subtype.

--  Partial views of deferred constants may be in Alfa even if their full view
--  is not in Alfa. This is the case if the type of the constant is in Alfa,
--  while its initializing expression is not.

with Types;          use Types;

with Gnat2Why.Nodes; use Gnat2Why.Nodes;

package SPARK_Definition is

   Spec_Entities : List_Of_Nodes.List;
   Body_Entities : List_Of_Nodes.List;
   --  Lists of entities which are defined in the current unit, that require
   --  a translation in Why3. One is for entities defined in the spec, and the
   --  other for entities defined in the body. These lists contains both
   --  entities in Alfa and entities not in Alfa. Each entity may be
   --  attached to a declaration or not (for Itypes).

   All_Entities : Node_Sets.Set;
   --  Set of all entities marked so far. This contains both entities from the
   --  current compiled unit, and also entities from other units.

   procedure Before_Marking (Filename : String);
   --  Create a file to store detailed information about the Alfa status of
   --  subprograms (spec/body in Alfa or not). Set a flag that allows marking
   --  of entities.

   procedure After_Marking;
   --  Close the file created by Before_Marking and unset the flag that allows
   --  marking of entities.

   procedure Mark_Compilation_Unit (N : Node_Id);
   --  Put marks on a compilation unit. This should be called after all
   --  compilation units on which it depends have been marked.

   procedure Mark_Standard_Package;
   --  Put marks on package Standard

   function In_Alfa (Id : Entity_Id) return Boolean;
   --  Return whether the entity Id is in Alfa

   function Body_In_Alfa (Id : Entity_Id) return Boolean;
   --  Return whether the body of subprogram Id is in Alfa

end SPARK_Definition;
