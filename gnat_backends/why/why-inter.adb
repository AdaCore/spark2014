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

with Sinfo;         use Sinfo;
with Einfo;         use Einfo;
with Atree;         use Atree;
with Constant_Tree;

package body Why.Inter is

   package Type_Hierarchy is
     new Constant_Tree (Ext_Why_Base, Why_Null_Type);

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

   ---------
   -- LCA --
   ---------

   function  LCA (Left, Right : Why_Type) return Why_Type is
   begin
      if Left = Right then
         return Left;
      else
         return Why_Types
           (Type_Hierarchy.LCA
             (Base_Why_Type (Left).Kind,
              Base_Why_Type (Right).Kind));
      end if;
   end LCA;

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

   --------
   -- Up --
   --------

   function Up (WT : Why_Type) return Why_Type is
   begin
      case WT.Kind is
         when Why_Abstract =>
            return Base_Why_Type (WT);
         when others =>
            return Why_Types (Type_Hierarchy.Up (WT.Kind));
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

begin
   Type_Hierarchy.Move_Child (Why_Null_Type, Why_Real);
   Type_Hierarchy.Move_Child (Why_Int, Why_Bool);
   Type_Hierarchy.Move_Child (Why_Real, Why_Int);
   Type_Hierarchy.Move_Child (Why_Real, Why_Fixed_Point);
   Type_Hierarchy.Freeze;
end Why.Inter;
