------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                 Copyright (C) 2016-2017, Altran UK Limited               --
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
with Atree;       use Atree;
with Einfo;       use Einfo;
with Lib.Xref;
with Sem_Util;    use Sem_Util;
with Sinfo;       use Sinfo;
with SPARK_Util;  use SPARK_Util;

package body Flow_Generated_Globals.Traversal is

   Entity_Tree : Node_Trees.Tree;
   --  Hierarchical container with entities processed by the flow analysis,
   --  i.e. packages, subprograms, entries and task types. The hierarchy of
   --  its contents mirrors the hierarchy of the analyzed code; the ordering of
   --  siblings is that packages go first and subprograms/entries/task types go
   --  after them.

   Current_Scope       : Node_Trees.Cursor := Entity_Tree.Root;
   First_Non_Pkg_Scope : Node_Trees.Cursor := Node_Trees.No_Element;
   --  Cursors to the current package/subprogram/entry/task type (which are the
   --  entities processed by the flow analyzis) and to the first non-package
   --  inserted under the current scope (sibling packages goes first and then
   --  go other entities).

   procedure Build_Tree (CU : Node_Id) is

      Debug : constant Boolean := False;

      use type Node_Trees.Cursor;

      subtype Container_Scope is Entity_Kind
        with Static_Predicate => Container_Scope in Entry_Kind       |
                                                    E_Function       |
                                                    E_Package        |
                                                    E_Procedure      |
                                                    E_Protected_Type |
                                                    E_Task_Type;

      procedure Enter_Spec (E : Entity_Id)
        with Pre => Ekind (E) in Container_Scope;
      --  Create new scope in the scope tree and enter it

      procedure Enter_Body (Spec_E : Entity_Id)
        with Pre => Ekind (Spec_E) in Container_Scope;
      --  Forward Current_Scope to the spec of E and enter it; only for bodies

      function Save return Tree_Cursor;
      --  Returns a copy of the cursor to first non-pkg child

      procedure Restore (Old : Tree_Cursor);
      --  Restore current tree cursor from a copy; if Is_Package is false and
      --  we are in the first non-package child of the current scope then cache
      --  it.

      procedure Process (N : Node_Id);
      --  Process declaration to build the hierarchical scope structure

      procedure Traverse is new
        Lib.Xref.SPARK_Specific.Traverse_Compilation_Unit (Process);

      ----------------
      -- Enter_Body --
      ----------------

      procedure Enter_Body (Spec_E : Entity_Id) is
      begin
         if Debug then
            for D in 0 .. Node_Trees.Depth (Current_Scope) loop
               Ada.Text_IO.Put (" ");
            end loop;
            Ada.Text_IO.Put_Line (Full_Source_Name (Spec_E) & " (body)");
         end if;

         --  First forward the current scope
         Current_Scope := Node_Trees.First_Child (Current_Scope);
         loop
            pragma Loop_Invariant (Node_Trees.Has_Element (Current_Scope));
            if Entity_Tree (Current_Scope) = Spec_E then
               exit;
            end if;
            Node_Trees.Next_Sibling (Current_Scope);
         end loop;

         --  Then the first non-pkg scope
         First_Non_Pkg_Scope := Node_Trees.First_Child (Current_Scope);
         while Node_Trees.Has_Element (First_Non_Pkg_Scope)
           and then
             Ekind (Node_Trees.Element (First_Non_Pkg_Scope)) = E_Package
         loop
            Node_Trees.Next_Sibling (First_Non_Pkg_Scope);
         end loop;
      end Enter_Body;

      ----------------
      -- Enter_Spec --
      ----------------

      procedure Enter_Spec (E : Entity_Id) is
      begin
         if Debug then
            for D in 0 .. Node_Trees.Depth (Current_Scope) loop
               Ada.Text_IO.Put (" ");
            end loop;
            Ada.Text_IO.Put_Line (Full_Source_Name (E));
         end if;

         Entity_Tree.Insert_Child
           (Parent   => Current_Scope,
            Before   => (if Ekind (E) = E_Package
                         then First_Non_Pkg_Scope
                         else Node_Trees.No_Element),
            New_Item => E,
            Position => Current_Scope);
         First_Non_Pkg_Scope := Node_Trees.No_Element;
      end Enter_Spec;

      -------------
      -- Process --
      -------------

      procedure Process (N : Node_Id) is
      begin
         case Nkind (N) is
            when N_Entry_Declaration          |
                 N_Package_Declaration        |
                 N_Protected_Type_Declaration |
                 N_Subprogram_Declaration     |
                 N_Task_Type_Declaration      =>
               declare
                  Scopes : constant Tree_Cursor := Save;
               begin
                  Enter_Spec (Defining_Entity (N));
                  Restore (Scopes);
               end;

            when N_Entry_Body      |
                 N_Package_Body    |
                 N_Protected_Body  |
                 N_Subprogram_Body |
                 N_Task_Body       =>

               declare
                  E : constant Entity_Id := Unique_Defining_Entity (N);
               begin
                  --  Skip bodies of generic packages and subprograms; also
                  --  subprograms that front-end generates to analyze default
                  --  expressions, see Mark_Subprogram_Body for details.
                  if (Nkind (N) = N_Package_Body and then
                        Ekind (E) = E_Generic_Package)
                    or else
                      (Nkind (N) = N_Subprogram_Body and then
                       (Is_Generic_Subprogram (E) or else
                        (Is_Eliminated (E) and not Comes_From_Source (E))))
                  then
                     return;
                  end if;

                  declare
                     Scopes : constant Tree_Cursor := Save;
                  begin
                     if Nkind (N) = N_Subprogram_Body
                       and then Acts_As_Spec (N)
                     then
                        --  ??? this can be optimized
                        Enter_Spec (E);
                        Restore (Scopes);
                     end if;
                     Enter_Body (E);
                     Restore (Scopes);
                  end;
               end;

            --  Subprogram stubs may act as declarations ???

            when N_Subprogram_Body_Stub =>
               declare
                  E      : constant Entity_Id := Unique_Defining_Entity (N);
                  Scopes : constant Tree_Cursor := Save;
               begin
                  if No (Corresponding_Spec_Of_Stub (N)) then
                     Enter_Spec (E);
                     Restore (Scopes);
                  end if;
                  Enter_Body (E);
                  Restore (Scopes);
               end;

            when others =>
               null;
         end case;
      end Process;

      -------------
      -- Restore --
      -------------

      procedure Restore (Old : Tree_Cursor)
      is
         Is_Package : constant Boolean :=
           (Ekind (Entity_Tree (Current_Scope)) = E_Package);

      begin
         First_Non_Pkg_Scope :=
           (if not Is_Package
            and then Old = Node_Trees.No_Element
            then Current_Scope
            else Old);
         Current_Scope := Node_Trees.Parent (Current_Scope);
      end Restore;

      ----------
      -- Save --
      ----------

      function Save return Tree_Cursor is
      begin
         return First_Non_Pkg_Scope;
      end Save;

   --  Start of processing for Build_Tree

   begin
      pragma Assert (Current_Scope = Entity_Tree.Root);

      Traverse (CU, Inside_Stubs => True);

      pragma Assert (Current_Scope = Entity_Tree.Root);
   end Build_Tree;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Process : not null access procedure (E : Entity_Id))
   is

      procedure Iterate_Subtree (Subtree : Node_Trees.Cursor);

      ---------------------
      -- Iterate_Subtree --
      ---------------------

      procedure Iterate_Subtree (Subtree : Node_Trees.Cursor) is
         Debug_Tree_Traversal : constant Boolean := False;
         --  Display the entity name as the entity tree is traversed

      begin
         --  This is a helper function to recursively iterate over all the
         --  nodes in a subtree, in depth-first fashion. It first visits the
         --  children and then the root.

         Node_Trees.Iterate_Children (Parent  => Subtree,
                                      Process => Iterate_Subtree'Access);
         Process (Entity_Tree (Subtree));

         if Debug_Tree_Traversal then
            Ada.Text_IO.Put
              (Ada.Containers.Count_Type'Image
                 (Node_Trees.Depth (Subtree)));
            Ada.Text_IO.Put (" ");
            Ada.Text_IO.Put_Line
              (To_String
                 (To_Entity_Name (Entity_Tree (Subtree))));
         end if;
      end Iterate_Subtree;

      --  Start of processing for Iterate_Entities

   begin
      Node_Trees.Iterate_Children (Parent  => Entity_Tree.Root,
                                   Process => Iterate_Subtree'Access);
   end Iterate;

   -----------------
   -- Root_Entity --
   -----------------

   function Root_Entity return Tree_Cursor is (Entity_Tree.Root);

end Flow_Generated_Globals.Traversal;
