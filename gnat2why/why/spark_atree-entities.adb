------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ A T R E E . E N T I T I E S                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2018, AdaCore                        --
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

with Atree;            use Atree;
with Opt;              use type Opt.Ada_Version_Type;
with Sem_Aux;
with Sem_Util;
with Sem_Prag;
with SPARK_Util.Types;
with Ttypes;

package body SPARK_Atree.Entities is

   ---------------
   -- Alignment --
   ---------------

   function Alignment (Typ : Entity_Id) return Uint renames Einfo.Alignment;

   ---------------
   -- Base_Type --
   ---------------

   function Base_Type (Typ : Entity_Id) return Entity_Id renames
     Einfo.Base_Type;

   --------------------
   -- Cloned_Subtype --
   --------------------

   function Cloned_Subtype (Typ : Entity_Id) return Entity_Id renames
     Einfo.Cloned_Subtype;

   ----------------------
   -- Component_Clause --
   ----------------------

   function Component_Clause (Obj : Entity_Id) return Node_Id renames
     Einfo.Component_Clause;

   -------------------------
   -- Component_First_Bit --
   -------------------------

   function Component_First_Bit (Obj : Entity_Id) return Uint is
   begin
      if Present (Component_Clause (Obj))
        and then Opt.Ada_Version >= Opt.Ada_2005
        and then Einfo.Reverse_Bit_Order (Sinfo.Scope (Obj))
      then
         return Expr_Value (First_Bit (Component_Clause (Obj)));
      else
         pragma Assert (Einfo.Known_Normalized_First_Bit (Obj));
         return Einfo.Normalized_First_Bit (Obj);
      end if;
   end Component_First_Bit;

   ------------------------
   -- Component_Last_Bit --
   ------------------------

   function Component_Last_Bit (Obj : Entity_Id) return Uint is
   begin
      if Present (Component_Clause (Obj))
        and then Opt.Ada_Version >= Opt.Ada_2005
        and then Einfo.Reverse_Bit_Order (Sinfo.Scope (Obj))
      then
         return Expr_Value (Last_Bit (Component_Clause (Obj)));

      else
         pragma Assert (Einfo.Known_Static_Component_Bit_Offset (Obj)
                        and then Einfo.Known_Static_Esize (Obj));
         return Einfo.Component_Bit_Offset (Obj) mod
           Ttypes.System_Storage_Unit + Einfo.Esize (Obj) - 1;
      end if;
   end Component_Last_Bit;

   ------------------------
   -- Component_Position --
   ------------------------

   function Component_Position (Obj : Entity_Id) return Uint is
   begin
      if Opt.Ada_Version >= Opt.Ada_2005
        and then Einfo.Reverse_Bit_Order (Sinfo.Scope (Obj))
      then
         return Expr_Value (Sinfo.Position (Component_Clause (Obj)));
      else
         return Einfo.Normalized_Position (Obj);
      end if;
   end Component_Position;

   --------------------
   -- Component_Type --
   --------------------

   function Component_Type (Typ : Entity_Id) return Entity_Id renames
     Einfo.Component_Type;

   --------------------
   -- Constant_Value --
   --------------------

   function Constant_Value (Obj : Entity_Id) return Node_Id renames
     Sem_Aux.Constant_Value;

   ------------------------------------
   -- Default_Aspect_Component_Value --
   ------------------------------------

   function Default_Aspect_Component_Value (Typ : Entity_Id) return Node_Id is
     (Einfo.Default_Aspect_Component_Value
        (SPARK_Util.Types.Base_Retysp (Typ)));

   --------------------------
   -- Default_Aspect_Value --
   --------------------------

   function Default_Aspect_Value (Typ : Entity_Id) return Node_Id is
     (Einfo.Default_Aspect_Value (SPARK_Util.Types.Base_Retysp (Typ)));

   -------------------
   -- DIC_Procedure --
   -------------------

   function DIC_Procedure (Typ : Entity_Id) return Entity_Id renames
     Einfo.DIC_Procedure;

   ----------------------
   -- Discriminal_Link --
   ----------------------

   function Discriminal_Link (Obj : Entity_Id) return Node_Id renames
     Einfo.Discriminal_Link;

   -----------------------------
   -- Discriminant_Constraint --
   -----------------------------

   function Discriminant_Constraint (Typ : Entity_Id) return Elist_Id renames
     Einfo.Discriminant_Constraint;

   --------------------------------
   -- Discriminant_Default_Value --
   --------------------------------

   function Discriminant_Default_Value (Obj : Entity_Id) return Node_Id renames
     Einfo.Discriminant_Default_Value;

   ---------------------------
   -- Enclosing_Declaration --
   ---------------------------

   function Enclosing_Declaration (Obj : Entity_Id) return Entity_Id renames
     Atree.Parent;

   --------------------
   -- Enclosing_Type --
   --------------------

   function Enclosing_Type (Obj : Entity_Id) return Node_Id renames
     Sinfo.Scope;

   ---------------------
   -- Enumeration_Pos --
   ---------------------

   function Enumeration_Pos (Obj : Entity_Id) return Uint renames
     Einfo.Enumeration_Pos;

   ------------------------
   -- First_Discriminant --
   ------------------------

   function First_Discriminant (Typ : Entity_Id) return Entity_Id is
      Discr : Entity_Id := Sem_Aux.First_Discriminant (Typ);
   begin
      loop
         if SPARK_Util.Is_Not_Hidden_Discriminant (Discr) then
            return Discr;
         end if;
         Einfo.Next_Discriminant (Discr);
         exit when No (Discr);
      end loop;

      raise Program_Error;
   end First_Discriminant;

   ------------------
   -- First_Formal --
   ------------------

   function First_Formal (Subp : Entity_Id) return Entity_Id renames
     Einfo.First_Formal;

   -----------------
   -- First_Index --
   -----------------

   function First_Index (Typ : Entity_Id) return Node_Id renames
     Einfo.First_Index;

   -------------------
   -- First_Subtype --
   -------------------

   function First_Subtype (Typ : Entity_Id) return Entity_Id renames
     Sem_Aux.First_Subtype;

   ---------------
   -- Full_View --
   ---------------

   function Full_View (Obj : Entity_Id) return Entity_Id renames
     Einfo.Full_View;

   ---------------------
   -- Get_Cursor_Type --
   ---------------------

   function Get_Cursor_Type (Typ : Entity_Id) return Entity_Id renames
     Sem_Util.Get_Cursor_Type;

   ------------------------
   -- Has_Attach_Handler --
   ------------------------

   function Has_Attach_Handler (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Attach_Handler;

   ----------------------------
   -- Has_Controlling_Result --
   ----------------------------

   function Has_Controlling_Result (Subp : Entity_Id) return Boolean renames
     Einfo.Has_Controlling_Result;

   ------------------------
   -- Has_Default_Aspect --
   ------------------------

   function Has_Default_Aspect (Typ : Entity_Id) return Boolean is
     (Einfo.Has_Default_Aspect (SPARK_Util.Types.Base_Retysp (Typ)));

   ---------------------------------
   -- Has_Defaulted_Discriminants --
   ---------------------------------

   function Has_Defaulted_Discriminants
     (Typ : Entity_Id) return Boolean
      renames Sem_Util.Has_Defaulted_Discriminants;

   -------------
   -- Has_DIC --
   -------------

   function Has_DIC (Typ : Entity_Id) return Boolean renames Einfo.Has_DIC;

   -----------------------
   -- Has_Discriminants --
   -----------------------

   function Has_Discriminants (Typ : Entity_Id) return Boolean is
   begin
      if not Einfo.Has_Discriminants (Typ)
        and then not Einfo.Has_Unknown_Discriminants (Typ)
      then
         return False;
      end if;

      declare
         Discr : Entity_Id := Sem_Aux.First_Discriminant (Typ);
      begin
         loop
            if SPARK_Util.Is_Not_Hidden_Discriminant (Discr) then
               return True;
            end if;
            Einfo.Next_Discriminant (Discr);
            exit when No (Discr);
         end loop;
         return False;
      end;
   end Has_Discriminants;

   ---------------------------
   -- Has_Interrupt_Handler --
   ---------------------------

   function Has_Interrupt_Handler (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Interrupt_Handler;

   ----------------------------------
   -- Has_Pragma_Volatile_Function --
   ----------------------------------

   function Has_Pragma_Volatile_Function (Subp : Entity_Id) return Boolean is
     (Sem_Prag.Is_Enabled_Pragma
        (Get_Pragma (Subp, Pragma_Volatile_Function)));

   --------------------
   -- Has_Predicates --
   --------------------

   function Has_Predicates (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Predicates;

   -------------------------
   -- Invariant_Procedure --
   -------------------------

   function Invariant_Procedure (Typ : Entity_Id) return Entity_Id renames
     Einfo.Invariant_Procedure;

   -----------------------
   -- Is_Actual_Subtype --
   -----------------------

   function Is_Actual_Subtype (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Actual_Subtype;

   ------------------------
   -- Is_Class_Wide_Type --
   ------------------------

   function Is_Class_Wide_Type (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Class_Wide_Type;

   --------------------
   -- Is_Constrained --
   --------------------

   function Is_Constrained (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Constrained;

   --------------------
   -- Is_Entity_Name --
   --------------------

   function Is_Entity_Name (N : Node_Id) return Boolean renames
     Einfo.Is_Entity_Name;

   ---------------------
   -- Is_Limited_View --
   ---------------------

   function Is_Limited_View (Typ : Entity_Id) return Boolean renames
     Sem_Aux.Is_Limited_View;

   ---------------------------
   -- Is_Predicate_Function --
   ---------------------------

   function Is_Predicate_Function (Subp : Entity_Id) return Boolean renames
     Einfo.Is_Predicate_Function;

   --------------------
   -- Is_Tagged_Type --
   --------------------

   function Is_Tagged_Type (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Tagged_Type;

   --------------------------------------
   -- Is_Visible_Dispatching_Operation --
   --------------------------------------

   function Is_Visible_Dispatching_Operation (Subp : Entity_Id) return Boolean
   is (Einfo.Is_Dispatching_Operation (Subp)
       and then Present (SPARK_Util.Subprograms.Find_Dispatching_Type (Subp)));

   ------------------------
   -- Is_Wrapper_Package --
   ------------------------

   function Is_Wrapper_Package (Pack : Entity_Id) return Boolean renames
     Einfo.Is_Wrapper_Package;

   ---------------------
   -- Known_Alignment --
   ---------------------

   function Known_Alignment (Typ : Entity_Id) return Boolean renames
     Einfo.Known_Alignment;

   -------------------------------
   -- Known_Component_First_Bit --
   -------------------------------

   function Known_Component_First_Bit (Obj : Entity_Id) return Boolean is
     ((Present (Component_Clause (Obj))
       and then Opt.Ada_Version >= Opt.Ada_2005
       and then Einfo.Reverse_Bit_Order (Sinfo.Scope (Obj)))
      or else Einfo.Known_Normalized_First_Bit (Obj));

   ------------------------------
   -- Known_Component_Last_Bit --
   ------------------------------

   function Known_Component_Last_Bit (Obj : Entity_Id) return Boolean is
     ((Present (Component_Clause (Obj))
       and then Opt.Ada_Version >= Opt.Ada_2005
       and then Einfo.Reverse_Bit_Order (Sinfo.Scope (Obj)))
      or else (Einfo.Known_Static_Component_Bit_Offset (Obj)
               and then Einfo.Known_Static_Component_Size (Obj)));

   -----------------------
   -- Known_Object_Size --
   -----------------------

   function Known_Object_Size (Typ : Entity_Id) return Boolean renames
     Einfo.Known_Esize;

   ------------------
   -- Modular_Size --
   ------------------

   function Modular_Size (Typ : Entity_Id) return Uint renames Einfo.Esize;

   -------------
   -- Modulus --
   -------------

   function Modulus (Typ : Entity_Id) return Uint is
     (Einfo.Modulus (SPARK_Util.Types.Base_Retysp (Typ)));

   -----------------------
   -- Next_Discriminant --
   -----------------------

   procedure Next_Discriminant (Discr : in out Entity_Id) is
   begin
      loop
         Einfo.Next_Discriminant (Discr);
         exit when No (Discr)
           or else SPARK_Util.Is_Not_Hidden_Discriminant (Discr);
      end loop;
   end Next_Discriminant;

   -----------------------
   -- No_Binary_Modulus --
   -----------------------

   function Non_Binary_Modulus (Typ : Entity_Id) return Boolean is
     (Einfo.Non_Binary_Modulus (SPARK_Util.Types.Base_Retysp (Typ)));

   ------------------
   -- Null_Present --
   ------------------

   function Null_Present (Subp : Entity_Id) return Boolean is
     (Sinfo.Null_Present (Sem_Aux.Subprogram_Specification (Subp)));

   -----------------------
   -- Number_Dimensions --
   -----------------------

   function Number_Dimensions (Typ : Entity_Id) return Pos renames
     Einfo.Number_Dimensions;

   -----------------
   -- Object_Size --
   -----------------

   function Object_Size (Typ : Entity_Id) return Uint renames Einfo.Esize;

   ------------------
   -- Package_Body --
   ------------------

   function Package_Body (Pack : Entity_Id) return Node_Id renames
     Sem_Aux.Package_Body;

   ------------------------
   -- Predicate_Function --
   ------------------------

   function Predicate_Function (Typ : Entity_Id) return Entity_Id renames
     Einfo.Predicate_Function;

   -------------------------------------
   -- Private_Declarations_Of_Package --
   -------------------------------------

   function Private_Declarations_Of_Package (Pack : Entity_Id) return List_Id
   is (Sinfo.Private_Declarations (Sem_Aux.Package_Specification (Pack)));

   -----------------------
   -- Return_Applies_To --
   -----------------------

   function Return_Applies_To (E : Entity_Id) return Node_Id renames
     Einfo.Return_Applies_To;

   -----------------
   -- Small_Value --
   -----------------

   function Small_Value (Typ : Entity_Id) return Ureal renames
     Einfo.Small_Value;

   -----------------------
   -- Stored_Constraint --
   -----------------------

   function Stored_Constraint (Typ : Entity_Id) return Elist_Id renames
     Einfo.Stored_Constraint;

   ----------------------------
   --  String_Literal_Length --
   ----------------------------

   function String_Literal_Length (Typ : Entity_Id) return Uint renames
     Einfo.String_Literal_Length;

   -------------------------------
   --  String_Literal_Low_Bound --
   -------------------------------

   function String_Literal_Low_Bound (Typ : Entity_Id) return Node_Id renames
     Einfo.String_Literal_Low_Bound;

   -------------------------------
   --  Subprogram_Specification --
   -------------------------------

   function Subprogram_Specification (Subp : Entity_Id) return Node_Id is
     (if Einfo.Is_Entry (Subp) then Atree.Parent (Subp)
      else Sem_Aux.Subprogram_Specification (Subp));

   ---------------------
   -- Type_High_Bound --
   ---------------------

   function Type_High_Bound (Typ : Entity_Id) return Node_Id renames
     Einfo.Type_High_Bound;

   --------------------
   -- Type_Low_Bound --
   --------------------

   function Type_Low_Bound (Typ : Entity_Id) return Node_Id renames
     Einfo.Type_Low_Bound;

   -----------------------
   -- Ultimate_Ancestor --
   -----------------------

   function Ultimate_Ancestor (Typ : Entity_Id) return Entity_Id is
     (Sem_Aux.First_Subtype (Einfo.Root_Type (Einfo.Base_Type (Typ))));

   -------------------------------------
   -- Visible_Declarations_Of_Package --
   -------------------------------------

   function Visible_Declarations_Of_Package (Pack : Entity_Id) return List_Id
   is (Sinfo.Visible_Declarations (Sem_Aux.Package_Specification (Pack)));

end SPARK_Atree.Entities;
