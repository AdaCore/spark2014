------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ A T R E E . E N T I T I E S                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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
with Nlists;           use Nlists;
with Opt;              use type Opt.Ada_Version_Type;
with Sinfo;            use Sinfo;
with Sem_Ch7;          use Sem_Ch7;
with Sem_Util;
with Sem_Prag;
with SPARK_Util.Subprograms;
with SPARK_Util.Types;
with Ttypes;
with Interfaces;

package body SPARK_Atree.Entities is

   --------------------
   -- Actual_Subtype --
   --------------------

   function Actual_Subtype (Obj : Entity_Id) return Entity_Id renames
     Einfo.Actual_Subtype;

   ---------------
   -- Alignment --
   ---------------

   function Alignment (Ent : Entity_Id) return Uint renames Einfo.Alignment;

   -------------------------------
   -- Associated_Node_For_Itype --
   -------------------------------

   function Associated_Node_For_Itype (Id : Entity_Id) return Node_Id renames
     Einfo.Associated_Node_For_Itype;

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

   --------------------------------
   -- Designates_Incomplete_Type --
   --------------------------------

   function Designates_Incomplete_Type (E : Entity_Id) return Boolean is
     (Einfo.Is_Incomplete_Type (Einfo.Directly_Designated_Type (E))
      or else SPARK_Util.Is_Partial_View (Einfo.Directly_Designated_Type (E)));

   -------------------
   -- DIC_Procedure --
   -------------------

   function DIC_Procedure (Typ : Entity_Id) return Entity_Id renames
     Einfo.DIC_Procedure;

   ------------------------------
   -- Directly_Designated_Type --
   ------------------------------

   function Directly_Designated_Type (E : Entity_Id) return Node_Id is
      Des_Ty : constant Entity_Id := Einfo.Directly_Designated_Type (E);
   begin
      if Is_Incomplete_Type (Des_Ty) then
         return Einfo.Full_View (Des_Ty);
      else
         return Des_Ty;
      end if;
   end Directly_Designated_Type;

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

   function Enclosing_Declaration (E : Entity_Id) return Node_Id renames
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

   ---------------------
   -- Enumeration_Rep --
   ---------------------

   function Enumeration_Rep (Obj : Entity_Id) return Uint renames
     Einfo.Enumeration_Rep;

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

   function First_Formal (Subp : Entity_Id) return Entity_Id  is
      First : Entity_Id := Einfo.First_Formal (Subp);

   begin
      --  There should never be more than one formal for subp wrappers

      if Present (First)
        and then SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (First)
      then
         Einfo.Next_Formal (First);
      end if;
      return First;
   end First_Formal;

   -----------------
   -- First_Index --
   -----------------

   function First_Index (Typ : Entity_Id) return Node_Id renames
     Einfo.First_Index;

   -------------------
   -- First_Literal --
   -------------------

   function First_Literal (Typ : Entity_Id) return Entity_Id renames
     Einfo.First_Literal;

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

   ---------------------------
   -- Get_Enum_Lit_From_Pos --
   ---------------------------

   function Get_Enum_Lit_From_Pos (Typ : Entity_Id; P : Uint) return Entity_Id
   is (Sem_Util.Get_Enum_Lit_From_Pos (Typ, P, No_Location));

   ---------------------------------
   -- Get_Iterable_Type_Primitive --
   ---------------------------------

   function Get_Iterable_Type_Primitive
     (Typ : Entity_Id;
      Nam : Name_Id)
      return Entity_Id
   renames Sem_Util.Get_Iterable_Type_Primitive;

   ------------------
   -- Get_Rep_Item --
   ------------------

   function Get_Rep_Item (E : Entity_Id; Nam : Name_Id) return Node_Id is
   begin
      return Sem_Aux.Get_Rep_Item (E, Nam, True);
   end Get_Rep_Item;

   -------------------------
   -- Get_User_Defined_Eq --
   -------------------------

   function Get_User_Defined_Eq (Typ : Entity_Id) return Entity_Id is
      Eq : constant Entity_Id := Sem_Util.Get_User_Defined_Eq (Typ);
   begin
      if Present (Eq) and then Present (Einfo.Renamed_Entity (Eq)) then
         return Einfo.Renamed_Entity (Eq);
      end if;

      return Eq;
   end Get_User_Defined_Eq;

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
         while Present (Discr) loop
            if SPARK_Util.Is_Not_Hidden_Discriminant (Discr) then
               return True;
            end if;
            Einfo.Next_Discriminant (Discr);
         end loop;
         return False;
      end;
   end Has_Discriminants;

   --------------------------------
   -- Has_Enumeration_Rep_Clause --
   --------------------------------

   function Has_Enumeration_Rep_Clause (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Enumeration_Rep_Clause;

   ---------------------------
   -- Has_Interrupt_Handler --
   ---------------------------

   function Has_Interrupt_Handler (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Interrupt_Handler;

   -----------------
   -- Has_Own_DIC --
   -----------------

   function Has_Own_DIC (Typ : Entity_Id) return Boolean renames
     Einfo.Has_Own_DIC;

   ----------------------------------
   -- Has_Pragma_Volatile_Function --
   ----------------------------------

   function Has_Pragma_Volatile_Function (Subp : Entity_Id) return Boolean is
     ((Ekind (Subp) = E_Function
       and then Sem_Util.Is_Unchecked_Conversion_Instance (Subp)
       and then Sem_Util.Has_Effectively_Volatile_Profile (Subp))
      or else Sem_Prag.Is_Enabled_Pragma
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

   -------------------------------
   -- Is_Access_Subprogram_Type --
   -------------------------------

   function Is_Access_Subprogram_Type (E : Entity_Id) return Boolean is
     (Einfo.Is_Access_Type (E)
      and then Atree.Ekind (Einfo.Directly_Designated_Type (E)) =
        Einfo.E_Subprogram_Type);

   -----------------------
   -- Is_Actual_Subtype --
   -----------------------

   function Is_Actual_Subtype (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Actual_Subtype;

   ------------------
   -- Is_Base_Type --
   ------------------

   function Is_Base_Type (Typ : Entity_Id) return Boolean renames
     Einfo.Is_Base_Type;

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

   ------------------------------------------
   -- Is_Expression_Function_Or_Completion --
   ------------------------------------------

   function Is_Expression_Function_Or_Completion
     (Subp : Entity_Id)
      return Boolean
      renames Sem_Util.Is_Expression_Function_Or_Completion;

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
   -- Is_Unchecked_Conversion_Instance --
   --------------------------------------

   function Is_Unchecked_Conversion_Instance (Subp : Entity_Id) return Boolean
     renames Sem_Util.Is_Unchecked_Conversion_Instance;

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

   function Known_Alignment (Ent : Entity_Id) return Boolean renames
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

   ----------------------
   -- Known_To_Precede --
   ----------------------

   function Known_To_Precede (Withed, Main : Entity_Id) return Boolean is
      Main_Unit : constant Node_Id := Enclosing_Comp_Unit_Node (Main);
      Item      : Node_Id;
      Elab_Id   : Entity_Id;

   begin
      --  A body can with its own spec. Ignore this case here.

      if Unique_Entity (Withed) = Unique_Entity (Main) then
         return False;
      end if;

      --  The elaboration of the body of Withed is said to be known to precede
      --  the elaboration of Main if either:

      --  a. Main references Withed in an Elaborate or Elaborate_All pragma; or

      Item := First (Context_Items (Main_Unit));
      while Present (Item) loop
         if Nkind (Item) = N_Pragma
           and then Pragma_Name (Item) in Name_Elaborate | Name_Elaborate_All
         then
            Elab_Id :=
              Entity
                (Expression (First (Pragma_Argument_Associations (Item))));

            if Withed = Elab_Id then
               return True;
            end if;
         end if;

         Next (Item);
      end loop;

      --  b. Withed's Elaborate_Body aspect is True; or

      if Has_Pragma_Elaborate_Body (Withed) then
         return True;
      end if;

      --  c. Withed does not require a body (the terminology is a little odd in
      --     this case because Withed has no body); or

      if not Unit_Requires_Body (Withed) then
         return True;
      end if;

      --  d. Withed is preelaborated and Mains's library unit is not; or

      if Is_Preelaborated (Withed) and then not Is_Preelaborated (Main) then
         return True;
      end if;

      --  e. Main semantically depends on some library_item L3 such that the
      --     elaboration of the body of Withed is known to precede the
      --     elaboration of L3. [See Ada RM 10.1.1 for definition of semantic
      --     dependence.]

      --  We (conservatively) do not test for this condition currently.

      return False;

   end Known_To_Precede;

   --------------------------
   -- Max_Size_Of_Img_Attr --
   --------------------------

   function Max_Size_Of_Img_Attr (Typ : Entity_Id) return Uint is
      function Max_Size_Of_Integer (Size : Int) return Int is
        (Interfaces.Unsigned_64'Image (2 ** Natural (Size))'Length + 1);
      --  Maximal size of integer values (positive values are prefixed by a
      --  space).

   begin
      return
        (if Atree.Ekind (Typ) in Einfo.Integer_Kind then
            UI_From_Int (Max_Size_Of_Integer (UI_To_Int (Einfo.Esize (Typ))))

         --  Maximal size of an identifier:
         --    maximum_line_length (255) * length_of_a_wide_character (8)

         else UI_From_Int (255 * 8));
   end Max_Size_Of_Img_Attr;

   ------------------
   -- Modular_Size --
   ------------------

   function Modular_Size (Typ : Entity_Id) return Uint is
      M : constant Uint := Modulus (Typ);
   begin
      if M <= UI_Expon (Uint_2, Uint_8) then
         return Uint_8;
      elsif M <= UI_Expon (Uint_2, Uint_16) then
         return Uint_16;
      elsif M <= UI_Expon (Uint_2, Uint_32) then
         return Uint_32;
      elsif M <= UI_Expon (Uint_2, Uint_64) then
         return Uint_64;
      elsif M <= UI_Expon (Uint_2, Uint_128) then
         return Uint_128;
      else
         raise Program_Error;
      end if;
   end Modular_Size;

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

   -----------------
   -- Next_Formal --
   -----------------

   function Next_Formal (Formal : Entity_Id) return Entity_Id is
      Next : Entity_Id := Einfo.Next_Formal (Formal);

   begin
      --  There should never be more than one formal for subp wrappers

      if Present (Next)
        and then SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (Next)
      then
         Einfo.Next_Formal (Next);
      end if;
      return Next;
   end Next_Formal;

   procedure Next_Formal (Formal : in out Entity_Id) is
   begin
      Einfo.Next_Formal (Formal);

      --  There should never be more than one formal for subp wrappers

      if Present (Formal)
        and then SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (Formal)
      then
         Einfo.Next_Formal (Formal);
      end if;
   end Next_Formal;

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

   --------------------
   -- Number_Formals --
   --------------------

   function Number_Formals (Subp : Entity_Id) return Natural is
      N      : Natural := 0;
      Formal : Entity_Id := Einfo.First_Formal (Subp);
   begin
      while Present (Formal) loop
         if not SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (Formal)
         then
            N := N + 1;
         end if;
         Einfo.Next_Formal (Formal);
      end loop;

      return N;
   end Number_Formals;

   -----------------
   -- Object_Size --
   -----------------

   function Object_Size (Typ : Entity_Id) return Uint renames Einfo.Esize;

   ------------------
   -- Package_Body --
   ------------------

   function Package_Body (Pack : Entity_Id) return Node_Id renames
     Sem_Aux.Package_Body;

   -------------------------
   -- Package_Body_Entity --
   -------------------------

   function Package_Body_Entity (Pack : Node_Id) return Entity_Id is
      (Sem_Util.Defining_Entity (Pack));

   ------------------
   -- Package_Spec --
   ------------------

   function Package_Spec (Pack : Entity_Id) return Node_Id renames
     Sem_Aux.Package_Spec;

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

   function Type_Low_Bound (Typ : Entity_Id) return Node_Id is
     (if Ekind (Typ) = E_String_Literal_Subtype then
           String_Literal_Low_Bound (Typ)
      else Einfo.Type_Low_Bound (Typ));

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
