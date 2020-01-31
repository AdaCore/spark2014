------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--       F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 2        --
--                            T R A V E R S A L                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2018-2020, Altran UK Limited                --
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

with Ada.Text_IO;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;

package body Flow_Generated_Globals.Phase_2.Traversal is

   ---------------
   -- Dump_Tree --
   ---------------

   procedure Dump_Tree is

      procedure Dump_Tree (E : Entity_Name; Indent : Natural);

      ---------------
      -- Dump_Tree --
      ---------------

      procedure Dump_Tree (E : Entity_Name; Indent : Natural) is
      begin
         Ada.Text_IO.Put_Line (Indent * '*' & " " & To_String (E));
         for Child of Scope_Map (E) loop
            Dump_Tree (Child, Indent + 1);
         end loop;
      end Dump_Tree;

   --  Start of processing for Dump_Tree

   begin
      if XXX then
         Dump_Tree (Standard_Standard, Indent => 0);
      end if;
   end Dump_Tree;

   -------------
   -- Is_Leaf --
   -------------

   function Is_Leaf (E : Entity_Name) return Boolean is
     (Scope_Map (E).Units.Is_Empty);

   ------------------
   -- Parent_Scope --
   ------------------

   function Parent_Scope (E : Entity_Name) return Entity_Name is
     (Scope_Map (E).Parent);

   ----------------------------
   -- Register_Nested_Scopes --
   ----------------------------

   procedure Register_Nested_Scopes
     (Entity  : Entity_Name;
      Parents : Name_Lists.List)
   is
      Outer     : Entity_Name          := Standard_Standard;
      Outer_Pos : Nested_Scopes.Cursor := Scope_Map.Find (Standard_Standard);
      --  The outer scope (which we need to know when inserting the inner one)
      --  and its position in the map (which we need to know when populating
      --  the container with the nested units). We maintain this cursor to
      --  only lookup the map once for each name.

      Unused : Boolean;

   begin
      --  Register nesting pairs starting from Standard and the outermost
      --  parent.

      for Parent of reverse Parents loop
         Scope_Map (Outer_Pos).Units.Include (Parent);
         Scope_Map.Insert
           (Key      => Parent,
            New_Item => (Units => <>, Parent => Outer),
            Position => Outer_Pos,
            Inserted => Unused);

         Outer := Parent;
      end loop;

      --  Finally, register a pair of the innermost parent and the entity
      --  itself.

      Scope_Map (Outer_Pos).Units.Include (Entity);
      Scope_Map.Insert
        (Key      => Entity,
         New_Item => (Units => <>, Parent => Outer),
         Position => Outer_Pos,
         Inserted => Unused);

   end Register_Nested_Scopes;

   --------------------------
   -- Scope_Within_Or_Same --
   --------------------------

   function Scope_Within_Or_Same
     (Inner : Entity_Name;
      Outer : Entity_Name)
      return Boolean
   is
   begin
      --  Detect same scopes

      if Inner = Outer then
         return True;

      --  Detect Standard, which is the ultimate parent of all units

      elsif Inner = Standard_Standard then
         return False;

      --  For programs units analysed in phase 1, keep climbing the parentship
      --  hierarchy; all other units are not in our scope (e.g. subprograms in
      --  the predefined System package).

      else
         return Scope_Map.Contains (Inner)
           and then Scope_Within_Or_Same (Parent_Scope (Inner), Outer);
      end if;
   end Scope_Within_Or_Same;

begin
   --  Populate mapping with the standard unit, which an implicit parent of
   --  all units analysed in phase 1.

   Scope_Map.Insert
     (Key      => Standard_Standard,
      New_Item => (Units => <>, Parent => Null_Entity_Name));
   --  ??? Having this code in package elaboration means it is needlessly
   --  executed in phase 1. Ideally it should be done just before resolving
   --  globals in phase 2 and the container should be cleared afterwards, to
   --  free as much memory for provers as possible.
end Flow_Generated_Globals.Phase_2.Traversal;
