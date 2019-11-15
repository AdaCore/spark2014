------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                            T R A V E R S A L                             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2018-2019, Altran UK Limited                --
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

--  This package provides the hierarchy of Entity_Names. It mirrors a similar
--  package that we have for Entity_Ids, so those two should be kept in sync.

private package Flow_Generated_Globals.Phase_2.Traversal is

   procedure Register_Nested_Scopes
     (Entity  : Entity_Name;
      Parents : Name_Lists.List)
   with Pre => not Parents.Contains (Entity);
   --  In phase 1 we register the hierarchy relationship while traversing the
   --  AST; here we register it while reading the ALI files.

   procedure Dump_Tree;
   --  Display the hierarchy

   type Nested is record
      Units  : Name_Sets.Set;
      Parent : Any_Entity_Name;
   end record with
     Iterable => (First       => First_Cursor,
                  Next        => Next_Cursor,
                  Has_Element => Has_Element,
                  Element     => Get_Element);
   --  In phase 1 the Units component is intentionally a list, because while
   --  traversing the we encounter each program unit only once. Here it is
   --  a set, because we might encounter each program unit many times while
   --  processing ALI files of different child compilation units.

   function First_Cursor (Cont : Nested) return Name_Sets.Cursor;
   --  For aspect Iterable

   function Next_Cursor
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Name_Sets.Cursor;
   --  For aspect Iterable

   function Has_Element
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Boolean;
   --  For aspect Iterable

   function Get_Element
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Entity_Name;
   --  For aspect Iterable

   package Nested_Scopes is new
     Ada.Containers.Hashed_Maps (Key_Type        => Entity_Name,
                                 Element_Type    => Nested,
                                 Hash            => Name_Hash,
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

   function Is_Leaf (E : Entity_Name) return Boolean;
   --  Returns True iff E is a leaf of the traversal tree

   function Parent_Scope (E : Entity_Name) return Entity_Name;
   --  Returns the parent scope of E (in the flow nesting sense)

   function Scope_Within_Or_Same
     (Inner : Entity_Name;
      Outer : Entity_Name)
      return Boolean;
   --  Same as version for Entity_Ids, but for Entity_Names

private

   ------------------
   -- First_Cursor --
   ------------------

   function First_Cursor (Cont : Nested) return Name_Sets.Cursor is
     (Cont.Units.First);

   -----------------
   -- Next_Cursor --
   -----------------

   function Next_Cursor
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Name_Sets.Cursor
   is
     (Name_Sets.Next (Position));

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Boolean
   is
     (Name_Sets.Has_Element (Position));

   -----------------
   -- Get_Element --
   -----------------

   function Get_Element
     (Cont     : Nested;
      Position : Name_Sets.Cursor)
      return Entity_Name
   is
     (Name_Sets.Element (Position));

end Flow_Generated_Globals.Phase_2.Traversal;
