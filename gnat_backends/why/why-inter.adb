------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Sinfo; use Sinfo;
with Einfo; use Einfo;
with Atree; use Atree;

package body Why.Inter is

   type Type_Set is array (Ext_Why_Base) of Boolean;

   type BT_Node is record
      Parent         : Ext_Why_Base := Why_Null_Type;
      Is_Parent_Of   : Type_Set := (others => False);
      Is_Ancestor_Of : Type_Set := (others => False);
   end record;

   type BT_Tree is array (Ext_Why_Base) of BT_Node;

   T : BT_Tree;

   procedure Init_Ancestors;

   procedure Move_Child (Parent : Ext_Why_Base; Child : Ext_Why_Base);

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (P : out Why_Package; Name : String) is
   begin
      P.WP_Context.Append (Name);
   end Add_With_Clause;

   procedure Add_With_Clause (P : out Why_Package; Other : Why_Package) is
   begin
      P.WP_Context.Append (Other.WP_Name.all);
   end Add_With_Clause;

   -------------------
   -- Base_Why_Type --
   -------------------

   function Base_Why_Type (W : Why_Type) return Why_Type is
   begin
      case W.Kind is
         when Why_Abstract =>
            return Base_Why_Type (W.Wh_Abstract);
         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return Why_Type is
   begin
      case Ekind (Etype (N)) is
         when Float_Kind =>
            return Why_Real_Type;

         when Signed_Integer_Kind | Enumeration_Kind =>
            --  ??? What about booleans ? We should have
            --  a special case for them...
            return Why_Int_Type;

         when others =>
            raise Not_Implemented;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Why_Type) return Why_Type is
      L : constant Why_Type := Base_Why_Type (Left);
      R : constant Why_Type := Base_Why_Type (Right);
   begin
      if L.Kind = Why_Real or else R.Kind = Why_Real then
         return Why_Real_Type;
      else
         return Why_Int_Type;
      end if;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Node_Id) return Why_Type is
   begin
      return Base_Why_Type (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   -------------------------
   -- Make_Empty_Why_Pack --
   -------------------------

   function Make_Empty_Why_Pack (S : String) return Why_Package
   is
   begin
      return
        (WP_Name           => new String'(S),
         WP_Context        => String_Lists.Empty_List,
         WP_Types          => List_Of_Nodes.Empty_List,
         WP_Abstract_Types => List_Of_Nodes.Empty_List,
         WP_Abstract_Obj   => List_Of_Nodes.Empty_List,
         WP_Decls          => List_Of_Nodes.Empty_List,
         WP_Decls_As_Spec  => List_Of_Nodes.Empty_List);
   end Make_Empty_Why_Pack;

   ---------
   -- LCA --
   ---------

   function  LCA (Left, Right : Why_Type) return Why_Type is

      function LCA_Subtree
        (Root  : Ext_Why_Base;
         Left  : Ext_Why_Base;
         Right : Ext_Why_Base)
        return Ext_Why_Base;

      -----------------
      -- LCA_Subtree --
      -----------------

      function LCA_Subtree
        (Root  : Ext_Why_Base;
         Left  : Ext_Why_Base;
         Right : Ext_Why_Base)
        return Ext_Why_Base is
      begin
         if Left = Right then
            return Left;
         end if;

         if Left = Root or else Right = Root then
            return Root;
         end if;

         if T (Root).Is_Ancestor_Of (Left)
           and then T (Root).Is_Ancestor_Of (Right)
         then
            for Child in Why_Scalar_Enum'Range loop
               if T (Root).Is_Parent_Of (Child) then
                  declare
                     Subtree : constant Ext_Why_Base
                                 := LCA_Subtree (Child, Left, Right);
                  begin
                     if Subtree /= Why_Null_Type then
                        return Subtree;
                     end if;
                  end;
               end if;
            end loop;

            --  No child is ancestor for both nodes; so we have reached the
            --  the LCA.
            return Root;

         else
            --  Left and Right cannot be reached from this node; cut this
            --  branch.
            return Why_Null_Type;
         end if;
      end LCA_Subtree;

   begin
      if Left = Right then
         return Left;

      else
         return Why_Types
           (LCA_Subtree
            (Why_Null_Type,
             Base_Why_Type (Left).Kind,
             Base_Why_Type (Right).Kind));
      end if;
   end LCA;

   --------
   -- Up --
   --------

   function Up (WT : Why_Type) return Why_Type is
   begin
      case WT.Kind is
         when Why_Abstract =>
            return Base_Why_Type (WT);
         when others =>
            return Why_Types (T (WT.Kind).Parent);
      end case;
   end Up;

   --------
   -- Up --
   --------

   function Up (From, To : Why_Type) return Why_Type is
   begin
      if From = To then
         return From;
      else
         return Up (From);
      end if;
   end Up;

   ------------------
   -- Why_Abstract --
   ------------------

   function Why_Abstract (N : Node_Id) return Why_Type
   is
   begin
      return (Kind => Why_Abstract, Wh_Abstract => N);
   end Why_Abstract;

   ------------------
   -- Move_Child --
   ------------------

   procedure Move_Child (Parent : Ext_Why_Base; Child : Ext_Why_Base) is
      Old_Parent : constant Ext_Why_Base := T (Child).Parent;
   begin
      T (Old_Parent).Is_Parent_Of (Child) := False;
      T (Child).Parent := Parent;
      T (Parent).Is_Parent_Of (Child) := True;
   end Move_Child;

   procedure Init_Ancestors is

      procedure Init_Ancestors (From : Ext_Why_Base);

      procedure Init_Ancestors (From : Ext_Why_Base) is
      begin
         --  * a child with no children has no ancestors; as its ancestor
         --  set has been initialized to the empty set, keep it as it is;
         --  * otherwise, the ancestors of a node is the union of the
         --  ancestors of its children with the set of children ;
         --  so initialize its children, then do the merge.

         for Child in Why_Scalar_Enum loop
            if T (From).Is_Parent_Of (Child) then
               Init_Ancestors (Child);

               T (From).Is_Ancestor_Of (Child) := True;
               for Sub_Child in Why_Scalar_Enum loop
                  if T (Child).Is_Ancestor_Of (Sub_Child) then
                     T (From).Is_Ancestor_Of (Sub_Child) := True;
                  end if;
               end loop;
            end if;
         end loop;
      end Init_Ancestors;

   begin
      Init_Ancestors (Why_Null_Type);
   end Init_Ancestors;

begin
   --  Why_Null_Type is the root node. Start with a flat hierarchy:
   T (Why_Null_Type).Is_Parent_Of := (others => True);

   --  ...then move nodes around to build the tree:

   Move_Child (Why_Null_Type, Why_Real);
   Move_Child (Why_Real, Why_Int);
   Move_Child (Why_Real, Why_Fixed_Point);

   --  ...then compute ancestors:
   Init_Ancestors;
end Why.Inter;
