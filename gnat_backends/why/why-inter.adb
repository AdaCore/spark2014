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

with Ada.Characters.Handling;

with Einfo;               use Einfo;
with Sem_Util;            use Sem_Util;
with Stand;               use Stand;
with Constant_Tree;
with Why.Conversions;     use Why.Conversions;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Atree.Accessors; use Why.Atree.Accessors;

package body Why.Inter is

   package Type_Hierarchy is
     new Constant_Tree (EW_Base_Type, EW_Unit);

   function Get_EW_Term_Type (N : Node_Id) return EW_Type;

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
         when EW_Abstract =>
            return Base_Why_Type (W.Wh_Abstract);
         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return Why_Type is
      E  : constant EW_Type := Get_EW_Term_Type (N);
   begin
      case E is
         when EW_Abstract =>
            raise Not_Implemented;

         when others =>
            return Why_Types (E);
      end case;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Why_Type) return Why_Type is
   begin
      return LCA (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Node_Id) return Why_Type is
   begin
      return Base_Why_Type (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Entity_Id) return String is
   begin
      if N = Standard_Boolean then
         return "bool";
      else
         declare
            S : String := Unique_Name (N);
         begin

            --  In Why3, enumeration literals need to be upper case. Why2
            --  doesn't care, so we enforce upper case here

            if Ekind (N) = E_Enumeration_Literal then
               S (S'First) := Ada.Characters.Handling.To_Upper (S (S'First));
            end if;
            return S;
         end;
      end if;
   end Full_Name;

   -----------------
   -- Get_EW_Type --
   -----------------

   function Get_EW_Type (T : W_Primitive_Type_Id) return EW_Type is
   begin
      if Get_Kind (+T) = W_Base_Type then
         return Get_Base_Type (+T);
      else
         return EW_Abstract;
      end if;
   end Get_EW_Type;

   function Get_EW_Type (T : Node_Id) return EW_Type is
      E : constant EW_Type := Get_EW_Term_Type (T);
   begin
      case E is
         when EW_Scalar =>
            return E;
         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Type;

   ----------------------
   -- Get_EW_Term_Type --
   ----------------------

   function Get_EW_Term_Type (N : Node_Id) return EW_Type is
      Ty : Node_Id := N;
   begin
      if Nkind (N) /= N_Defining_Identifier
        or else not (Ekind (N) in Type_Kind) then
         Ty := Etype (N);
      end if;

      case Ekind (Ty) is
         when Float_Kind =>
            return EW_Real;

         when Signed_Integer_Kind | Enumeration_Kind =>
            --  ??? What about booleans ? We should have
            --  a special case for them...
            return EW_Int;

         when Private_Kind =>
            return Get_EW_Term_Type (Full_View (Ty));

         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Term_Type;

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
         when EW_Abstract =>
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

   -----------------
   -- EW_Abstract --
   -----------------

   function EW_Abstract (N : Node_Id) return Why_Type
   is
   begin
      return (Kind => EW_Abstract, Wh_Abstract => N);
   end EW_Abstract;

begin
   Type_Hierarchy.Move_Child (EW_Unit, EW_Real);
   Type_Hierarchy.Move_Child (EW_Int, EW_Bool);
   Type_Hierarchy.Move_Child (EW_Real, EW_Int);
   Type_Hierarchy.Freeze;
end Why.Inter;
