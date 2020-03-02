------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--     F L O W . G E N E R A T E D _ G L O B A L S . T R A V E R S A L      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2016-2020, Altran UK Limited                --
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
------------------------------------------------------------------------------

with Ada.Containers.Hashed_Maps;
with Gnat2Why_Args;

package Flow_Generated_Globals.Traversal is

   procedure Build_Tree (CU : Node_Id);
   --  Traverse compilation unit CU to build a traversal tree

   procedure Dump_Tree;

   type Nested is record
      Units  : Node_Lists.List;
      Parent : Entity_Id;
   end record with
     Iterable => (First       => First_Cursor,
                  Next        => Next_Cursor,
                  Has_Element => Has_Element,
                  Element     => Get_Element);
   --  ??? add some type predicate

   function First_Cursor (Cont : Nested) return Node_Lists.Cursor;
   --  For aspect Iterable

   function Next_Cursor
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Node_Lists.Cursor;
   --  For aspect Iterable

   function Has_Element
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Boolean;
   --  For aspect Iterable

   function Get_Element
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Entity_Id;
   --  For aspect Iterable

   package Nested_Scopes is new
     Ada.Containers.Hashed_Maps (Key_Type        => Entity_Id,
                                 Element_Type    => Nested,
                                 Hash            => Node_Hash,
                                 Equivalent_Keys => "=",
                                 "="             => "=");

   Scope_Map : Nested_Scopes.Map;
   --  Hierarchical container with entities processed by the flow analysis,
   --  i.e. functions, procedures, entries (collectively known as subprograms)
   --  and packages, protected types and task types (collectively known as
   --  packages, sic). The hierarchy of its contents mirrors the hierarchy
   --  of the analyzed code.
   --
   --  ??? this is publicly visible only to make iteration easier

   subtype Container_Scope is Entity_Kind
     with Static_Predicate => Container_Scope in Entry_Kind       |
                                                 E_Function       |
                                                 E_Package        |
                                                 E_Procedure      |
                                                 E_Protected_Type |
                                                 E_Task_Type;
   --  ??? subtype from Checked_Entity_Id

   function Root_Entity return Entity_Id
   with Post => No (Root_Entity'Result)
                  or else
                Ekind (Root_Entity'Result) in Container_Scope;
   --  Returns a cursor for the root scope; for custom iteration

   function Is_Leaf (E : Entity_Id) return Boolean;
   --  Returns True iff E is a leaf of the traversal tree

   function Parent_Scope (E : Entity_Id) return Entity_Id
   with Pre  => Ekind (E) in Container_Scope,
        Post => Ekind (Parent_Scope'Result) in Container_Scope;
   --  Returns the parent scope of E (in the flow nesting sense)

   procedure Iterate_Main_Unit
     (Process : not null access procedure (E : Entity_Id));
   --  Iterate over scopes of the main unit in bottom-up fashion
   --  ??? deprecated

   generic
      with procedure Process (E : Entity_Id);
   procedure Iterate_Constants_In_Main_Unit
   with Pre => Gnat2Why_Args.Global_Gen_Mode;
   --  Call Process on constants in the current compilation unit; it is only
   --  available (and needed) in phase 1.

private

   ------------------
   -- First_Cursor --
   ------------------

   function First_Cursor (Cont : Nested) return Node_Lists.Cursor is
     (Cont.Units.First);

   -----------------
   -- Next_Cursor --
   -----------------

   function Next_Cursor
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Node_Lists.Cursor
   is
     (Node_Lists.Next (Position));

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Boolean
   is
     (Node_Lists.Has_Element (Position));

   -----------------
   -- Get_Element --
   -----------------

   function Get_Element
     (Cont     : Nested;
      Position : Node_Lists.Cursor)
      return Entity_Id
   is
     (Node_Lists.Element (Position));

end Flow_Generated_Globals.Traversal;
