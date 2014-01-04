------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        C O N S T A N T _ T R E E                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

package body Constant_Tree is

   type Node_Set is array (Node_Type) of Boolean;

   type Node_Info is record
      Parent         : Node_Type := Root;
      Is_Parent_Of   : Node_Set := (others => False);
      Is_Ancestor_Of : Node_Set := (others => False);
   end record;

   type Tree is array (Node_Type) of Node_Info;

   T : Tree;

   ------------
   -- Freeze --
   ------------

   procedure Freeze is

      procedure Init_Ancestors (From : Node_Type);
      --  Recursively init Is_Ancestor_Of, starting from the given node

      procedure Init_Ancestors (From : Node_Type) is
      begin
         --  * a node with no children has (a fortiori) no descendants;
         --  as its descendant set has been initialized to the empty
         --  set, keep it as it is;
         --
         --  * otherwise, the descendant set of a node is the union of the
         --  descendants of its children with the set of children;
         --  so initialize its children, then do the merge.

         for Child in Node_Type loop
            if T (From).Is_Parent_Of (Child) then
               Init_Ancestors (Child);

               T (From).Is_Ancestor_Of (Child) := True;
               for Sub_Child in Node_Type loop
                  if T (Child).Is_Ancestor_Of (Sub_Child) then
                     T (From).Is_Ancestor_Of (Sub_Child) := True;
                  end if;
               end loop;
            end if;
         end loop;
      end Init_Ancestors;

   begin
      Init_Ancestors (Root);
      Frozen := True;
   end Freeze;

   ---------
   -- LCA --
   ---------

   function  LCA (Left, Right : Node_Type) return Node_Type is

      function LCA_Subtree
        (From  : Node_Type;
         Left  : Node_Type;
         Right : Node_Type)
        return Node_Type;
      --  Assuming that From is a common ancestor of Left and Right,
      --  compute the LCA starting from From.

      -----------------
      -- LCA_Subtree --
      -----------------

      function LCA_Subtree
        (From  : Node_Type;
         Left  : Node_Type;
         Right : Node_Type)
        return Node_Type is
      begin
         if Left = Right then
            return Left;
         end if;

         if Left = From or else Right = From then
            return From;
         end if;

         if T (From).Is_Ancestor_Of (Left)
           and then T (From).Is_Ancestor_Of (Right)
         then
            for Child in Node_Type'Range loop
               if T (From).Is_Parent_Of (Child) then
                  declare
                     Subtree : constant Node_Type
                                 := LCA_Subtree (Child, Left, Right);
                  begin
                     if Subtree /= Root then
                        return Subtree;
                     end if;
                  end;
               end if;
            end loop;

            --  No child is ancestor for both nodes; so we have reached the
            --  the LCA.
            return From;

         else
            --  Left and Right cannot be reached from this node; cut this
            --  branch.
            return Root;
         end if;
      end LCA_Subtree;

   begin
      if Left = Right then
         return Left;
      else
         return LCA_Subtree (Root, Left, Right);
      end if;
   end LCA;

   ----------------
   -- Move_Child --
   ----------------

   procedure Move_Child (New_Parent : Node_Type; Child : Node_Type) is
      Old_Parent : constant Node_Type := T (Child).Parent;
   begin
      T (Old_Parent).Is_Parent_Of (Child) := False;
      T (Child).Parent := New_Parent;
      T (New_Parent).Is_Parent_Of (Child) := True;
   end Move_Child;

   --------
   -- Up --
   --------

   function Up (Node : Node_Type) return Node_Type is
   begin
      return T (Node).Parent;
   end Up;

   --------
   -- Up --
   --------

   function Up (From, To : Node_Type) return Node_Type is
   begin
      if From = To then
         return From;
      else
         return Up (From);
      end if;
   end Up;

begin
   --  Start with a flat hierarchy

   T (Root).Is_Parent_Of := (others => True);
   T (Root).Is_Parent_Of (Root) := False;
end Constant_Tree;
