------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ A T R E E . E N T I T I E S                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2023, AdaCore                     --
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
with Sinfo.Utils;      use Sinfo.Utils;
with Sem_Ch7;          use Sem_Ch7;
with Sem_Util;
with Sem_Prag;
with SPARK_Util.Types;
with Interfaces;

package body SPARK_Atree.Entities is

   --------------------
   -- Actual_Subtype --
   --------------------

   function Actual_Subtype (Obj : Object_Kind_Id) return Opt_Type_Kind_Id is
     (Einfo.Entities.Actual_Subtype (Obj));

   ---------------
   -- Alignment --
   ---------------

   function Alignment (Ent : Entity_Id) return Unat renames
     Einfo.Entities.Alignment;

   -------------------------------
   -- Associated_Node_For_Itype --
   -------------------------------

   function Associated_Node_For_Itype (Id : Type_Kind_Id) return Node_Id is
     (Einfo.Entities.Associated_Node_For_Itype (Id));

   ---------------
   -- Base_Type --
   ---------------

   function Base_Type (Typ : Type_Kind_Id) return Entity_Id is
     (Einfo.Utils.Base_Type (Typ));

   --------------------
   -- Cloned_Subtype --
   --------------------

   function Cloned_Subtype (Typ : Type_Kind_Id) return Entity_Id is
     (Einfo.Entities.Cloned_Subtype (Typ));

   --------------------
   -- Constant_Value --
   --------------------

   function Constant_Value (Obj : E_Constant_Id) return N_Subexpr_Id is
     (Sem_Aux.Constant_Value (Obj));

   ------------------------------------
   -- Default_Aspect_Component_Value --
   ------------------------------------

   function Default_Aspect_Component_Value
     (Typ : Array_Kind_Id)
      return Opt_N_Subexpr_Id
   is
     (Einfo.Entities.Default_Aspect_Component_Value
        (SPARK_Util.Types.Base_Retysp (Typ)));

   --------------------------
   -- Default_Aspect_Value --
   --------------------------

   function Default_Aspect_Value
     (Typ : Scalar_Kind_Id)
      return Opt_N_Subexpr_Id
   is
     (Einfo.Entities.Default_Aspect_Value
       (SPARK_Util.Types.Base_Retysp (Typ)));

   --------------------------------
   -- Designates_Incomplete_Type --
   --------------------------------

   function Designates_Incomplete_Type (E : Access_Kind_Id) return Boolean is
      Des_Ty : constant Type_Kind_Id :=
        Einfo.Entities.Directly_Designated_Type
          (SPARK_Util.Types.Base_Retysp (E));
      --  Use the base type as some subtypes of access to incomplete types
      --  introduced by the frontend designate record subtypes instead.
   begin
      return SPARK_Util.Types.Acts_As_Incomplete_Type (Des_Ty);
   end Designates_Incomplete_Type;

   ------------------------------
   -- Directly_Designated_Type --
   ------------------------------

   function Directly_Designated_Type (E : Access_Kind_Id) return Type_Kind_Id
   is
      Des_Ty : constant Type_Kind_Id :=
        Einfo.Entities.Directly_Designated_Type (E);
   begin
      if Einfo.Utils.Is_Incomplete_Type (Des_Ty)
        and then Present (Einfo.Entities.Full_View (Des_Ty))
      then
         return Einfo.Entities.Full_View (Des_Ty);
      else
         return Des_Ty;
      end if;
   end Directly_Designated_Type;

   ----------------------
   -- Discriminal_Link --
   ----------------------

   function Discriminal_Link (Obj : Object_Kind_Id) return E_Discriminant_Id is
     (Einfo.Entities.Discriminal_Link (Obj));

   -----------------------------
   -- Discriminant_Constraint --
   -----------------------------

   function Discriminant_Constraint (Typ : Type_Kind_Id) return Elist_Id is
     (Einfo.Entities.Discriminant_Constraint (Typ));

   --------------------------------
   -- Discriminant_Default_Value --
   --------------------------------

   function Discriminant_Default_Value
     (Obj : E_Discriminant_Id)
      return Opt_N_Subexpr_Id
   is (Einfo.Entities.Discriminant_Default_Value (Obj));

   ---------------------------
   -- Enclosing_Declaration --
   ---------------------------

   function Enclosing_Declaration (E : Entity_Id) return Node_Id renames
     Atree.Parent;

   --------------------
   -- Enclosing_Type --
   --------------------

   function Enclosing_Type (Obj : Entity_Id) return Type_Kind_Id is
     (Sinfo.Nodes.Scope (Obj));

   ------------------------
   -- First_Discriminant --
   ------------------------

   function First_Discriminant (Typ : Type_Kind_Id) return E_Discriminant_Id is
      (Sem_Aux.First_Discriminant (Typ));

   ------------------
   -- First_Formal --
   ------------------

   function First_Formal (Subp : Callable_Kind_Id) return Opt_Formal_Kind_Id is
      First : Entity_Id := Einfo.Utils.First_Formal (Subp);

   begin
      --  There should never be more than one formal for subp wrappers

      if Present (First)
        and then SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (First)
      then
         Einfo.Utils.Next_Formal (First);
      end if;
      return First;
   end First_Formal;

   ---------------
   -- Full_View --
   ---------------

   function Full_View (Obj : E_Constant_Id) return E_Constant_Id is
     (Einfo.Entities.Full_View (Obj));

   ---------------------
   -- Get_Cursor_Type --
   ---------------------

   function Get_Cursor_Type (Typ : Type_Kind_Id) return Entity_Id is
     (Sem_Util.Get_Cursor_Type (Typ));

   ---------------------------
   -- Get_Enum_Lit_From_Pos --
   ---------------------------

   function Get_Enum_Lit_From_Pos
     (Typ : Enumeration_Kind_Id;
      P   : Uint)
      return Node_Id
   is (Sem_Util.Get_Enum_Lit_From_Pos (Typ, P, No_Location));

   ---------------------------------
   -- Get_Iterable_Type_Primitive --
   ---------------------------------

   function Get_Iterable_Type_Primitive
     (Typ : Type_Kind_Id;
      Nam : Name_Id)
      return E_Function_Id
   is (Sem_Util.Get_Iterable_Type_Primitive (Typ, Nam));

   ------------------
   -- Get_Rep_Item --
   ------------------

   function Get_Rep_Item (E : Entity_Id; Nam : Name_Id) return Node_Id is
   begin
      return Sem_Aux.Get_Rep_Item (E, Nam, True);
   end Get_Rep_Item;

   ------------------------
   -- Has_Attach_Handler --
   ------------------------

   function Has_Attach_Handler (Typ : E_Protected_Type_Id) return Boolean is
     (Einfo.Utils.Has_Attach_Handler (Typ));

   ----------------------------
   -- Has_Controlling_Result --
   ----------------------------

   function Has_Controlling_Result (Subp : E_Function_Id) return Boolean is
     (Einfo.Entities.Has_Controlling_Result (Subp));

   ------------------------
   -- Has_Default_Aspect --
   ------------------------

   function Has_Default_Aspect (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Has_Default_Aspect (SPARK_Util.Types.Base_Retysp (Typ)));

   ---------------------------------
   -- Has_Defaulted_Discriminants --
   ---------------------------------

   function Has_Defaulted_Discriminants
     (Typ : Type_Kind_Id)
      return Boolean
   is (Sem_Util.Has_Defaulted_Discriminants (Typ));

   -------------
   -- Has_DIC --
   -------------

   function Has_DIC (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Utils.Has_DIC (Typ));

   -----------------------
   -- Has_Discriminants --
   -----------------------

   function Has_Discriminants (Typ : Type_Kind_Id) return Boolean is
   begin
      if not Einfo.Entities.Has_Discriminants (Typ)
        and then not Einfo.Entities.Has_Unknown_Discriminants (Typ)
      then
         return False;
      end if;

      --  If Type has discriminants in Ada, check that its discriminants are
      --  not hidden in SPARK. It can happen for subtypes of private types
      --  whose full view has discriminants but is not in SPARK and whose
      --  partial view does not have discriminants.

      declare
         Discr : constant Entity_Id := Sem_Aux.First_Discriminant (Typ);
      begin
         return Present (Discr)
           and then SPARK_Util.Is_Not_Hidden_Discriminant (Discr);
      end;
   end Has_Discriminants;

   ---------------------------
   -- Has_Interrupt_Handler --
   ---------------------------

   function Has_Interrupt_Handler (Typ : E_Protected_Type_Id) return Boolean is
     (Einfo.Utils.Has_Interrupt_Handler (Typ));

   ----------------------------------
   -- Has_Pragma_Volatile_Function --
   ----------------------------------

   function Has_Pragma_Volatile_Function
     (Subp : Callable_Kind_Id)
      return Boolean
   is
     ((Ekind (Subp) = E_Function
       and then Sem_Util.Is_Unchecked_Conversion_Instance (Subp)
       and then Sem_Util.Has_Effectively_Volatile_Profile (Subp))
      or else Sem_Prag.Is_Enabled_Pragma
        (Get_Pragma (Subp, Pragma_Volatile_Function)));

   --------------------
   -- Has_Predicates --
   --------------------

   function Has_Predicates (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Has_Predicates (Typ));

   -------------------------
   -- Invariant_Procedure --
   -------------------------

   function Invariant_Procedure (Typ : Type_Kind_Id) return Opt_E_Procedure_Id
   is (Einfo.Utils.Invariant_Procedure (Typ));

   ----------------------------
   -- Is_Abstract_Subprogram --
   ----------------------------

   function Is_Abstract_Subprogram (Subp : Callable_Kind_Id) return Boolean is
     (Einfo.Entities.Is_Abstract_Subprogram (Subp));

   -------------------------------
   -- Is_Access_Subprogram_Type --
   -------------------------------

   function Is_Access_Subprogram_Type (E : Type_Kind_Id) return Boolean is
     (Einfo.Utils.Is_Access_Type (E)
        and then
      Einfo.Entities.Ekind
        (Einfo.Entities.Directly_Designated_Type (E)) =
           Einfo.Entities.E_Subprogram_Type);

   ----------------
   -- Is_Aliased --
   ----------------

   function Is_Aliased (Obj : E_In_Parameter_Id) return Boolean is
     (Einfo.Entities.Is_Aliased (Obj));

   ------------------
   -- Is_Base_Type --
   ------------------

   function Is_Base_Type (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Utils.Is_Base_Type (Typ));

   ------------------------
   -- Is_Class_Wide_Type --
   ------------------------

   function Is_Class_Wide_Type (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Utils.Is_Class_Wide_Type (Typ));

   --------------------
   -- Is_Constrained --
   --------------------

   function Is_Constrained (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Is_Constrained (Typ));

   ------------------------------
   -- Is_Dispatching_Operation --
   ------------------------------

   function Is_Dispatching_Operation
     (Subp : Callable_Kind_Id)
      return Boolean
   is
     (Einfo.Entities.Is_Dispatching_Operation (Subp)
       and then Present (SPARK_Util.Subprograms.Find_Dispatching_Type (Subp)));

   --------------------
   -- Is_Entity_Name --
   --------------------

   function Is_Entity_Name (N : Node_Id) return Boolean renames
     Einfo.Utils.Is_Entity_Name;

   ------------------------------------------
   -- Is_Expression_Function_Or_Completion --
   ------------------------------------------

   function Is_Expression_Function_Or_Completion
     (Subp : Callable_Kind_Id)
      return Boolean
   is (Sem_Util.Is_Expression_Function_Or_Completion (Subp));

   ---------------------
   -- Is_Limited_View --
   ---------------------

   function Is_Limited_View (Typ : Type_Kind_Id) return Boolean is
     (Sem_Aux.Is_Limited_View (Typ));

   ---------------------------
   -- Is_Predicate_Function --
   ---------------------------

   function Is_Predicate_Function (Subp : Subprogram_Kind_Id) return Boolean is
     (Einfo.Entities.Is_Predicate_Function (Subp));

   --------------------
   -- Is_Tagged_Type --
   --------------------

   function Is_Tagged_Type (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Is_Tagged_Type (Typ));

   --------------------------------------
   -- Is_Unchecked_Conversion_Instance --
   --------------------------------------

   function Is_Unchecked_Conversion_Instance
     (Subp : Callable_Kind_Id)
      return Boolean
   is (Sem_Util.Is_Unchecked_Conversion_Instance (Subp));

   ------------------------
   -- Is_Unchecked_Union --
   ------------------------

   function Is_Unchecked_Union (E : Type_Kind_Id) return Boolean is
     (Einfo.Entities.Is_Unchecked_Union (SPARK_Util.Types.Base_Retysp (E)));

   ------------------------
   -- Is_Wrapper_Package --
   ------------------------

   function Is_Wrapper_Package (Pack : E_Package_Id) return Boolean is
     (Einfo.Utils.Is_Wrapper_Package (Pack));

   ---------------------
   -- Known_Alignment --
   ---------------------

   function Known_Alignment (Ent : Entity_Id) return Boolean renames
     Einfo.Utils.Known_Alignment;

   -------------------------------
   -- Known_Component_First_Bit --
   -------------------------------

   function Known_Component_First_Bit
     (Obj : Record_Field_Kind_Id)
      return Boolean
   is
     ((Present (Component_Clause (Obj))
       and then Opt.Ada_Version >= Opt.Ada_2005
       and then Einfo.Entities.Reverse_Bit_Order (Sinfo.Nodes.Scope (Obj)))
      or else Einfo.Utils.Known_Normalized_First_Bit (Obj));

   ------------------------------
   -- Known_Component_Last_Bit --
   ------------------------------

   function Known_Component_Last_Bit
     (Obj : Record_Field_Kind_Id)
      return Boolean
   is
     ((Present (Component_Clause (Obj))
       and then Opt.Ada_Version >= Opt.Ada_2005
       and then Einfo.Entities.Reverse_Bit_Order (Sinfo.Nodes.Scope (Obj)))
      or else (Einfo.Utils.Known_Static_Component_Bit_Offset (Obj)
               and then Einfo.Utils.Known_Static_Component_Size (Obj)));

   -----------------------
   -- Known_Object_Size --
   -----------------------

   function Known_Object_Size (Typ : Type_Kind_Id) return Boolean is
     (Einfo.Utils.Known_Esize (Typ));

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

      if Einfo.Entities.Has_Pragma_Elaborate_Body (Withed) then
         return True;
      end if;

      --  c. Withed does not require a body (the terminology is a little odd in
      --     this case because Withed has no body); or

      if not Unit_Requires_Body (Withed) then
         return True;
      end if;

      --  d. Withed is preelaborated and Mains's library unit is not; or

      if Einfo.Entities.Is_Preelaborated (Withed)
        and then not Einfo.Entities.Is_Preelaborated (Main)
      then
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

   function Max_Size_Of_Img_Attr (Typ : Scalar_Kind_Id) return Uint is
      use type Interfaces.Unsigned_64;

      function Max_Size_Of_Integer (Size : Int) return Int is
        (Interfaces.Unsigned_64'Image (2 ** Natural (Size))'Length + 1);
      --  Maximal size of integer values (positive values are prefixed by a
      --  space).

   begin
      return
        (if Einfo.Utils.Is_Integer_Type (Typ) then
            UI_From_Int
              (Max_Size_Of_Integer (UI_To_Int (Einfo.Entities.Esize (Typ))))
         --  Maximal size of an identifier:
         --    maximum_line_length (255) * length_of_a_wide_character (8)

         else UI_From_Int (255 * 8));
   end Max_Size_Of_Img_Attr;

   ------------------
   -- Modular_Size --
   ------------------

   function Modular_Size (Typ : Modular_Integer_Kind_Id) return Uint is
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

   function Modulus (Typ : Modular_Integer_Kind_Id) return Uint is
     (Einfo.Entities.Modulus (SPARK_Util.Types.Base_Retysp (Typ)));

   -----------------------
   -- Next_Discriminant --
   -----------------------

   procedure Next_Discriminant (Discr : in out Opt_E_Discriminant_Id) is
   begin
      Einfo.Utils.Next_Discriminant (Discr);
   end Next_Discriminant;

   -----------------
   -- Next_Formal --
   -----------------

   function Next_Formal (Formal : Formal_Kind_Id) return Opt_Formal_Kind_Id is
      Next : Entity_Id := Formal;

   begin
      Next_Formal (Next);
      return Next;
   end Next_Formal;

   procedure Next_Formal (Formal : in out Opt_Formal_Kind_Id) is
   begin
      Einfo.Utils.Next_Formal (Formal);

      --  There should never be more than one formal for subp wrappers

      if Present (Formal)
        and then SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (Formal)
      then
         Einfo.Utils.Next_Formal (Formal);
      end if;
   end Next_Formal;

   -----------------------
   -- No_Binary_Modulus --
   -----------------------

   function Non_Binary_Modulus (Typ : Modular_Integer_Kind_Id) return Boolean
   is (Einfo.Entities.Non_Binary_Modulus (SPARK_Util.Types.Base_Retysp (Typ)));

   ------------------
   -- Null_Present --
   ------------------

   function Null_Present (Subp : E_Procedure_Id) return Boolean is
     (Sinfo.Nodes.Null_Present (Sem_Aux.Subprogram_Specification (Subp)));

   -----------------------
   -- Number_Dimensions --
   -----------------------

   function Number_Dimensions (Typ : Array_Kind_Id) return Pos is
     (Einfo.Utils.Number_Dimensions (Typ));

   --------------------
   -- Number_Formals --
   --------------------

   function Number_Formals (Subp : Callable_Kind_Id) return Natural is
      N      : Natural := 0;
      Formal : Entity_Id := Einfo.Utils.First_Formal (Subp);
   begin
      while Present (Formal) loop
         if not SPARK_Util.Is_Additional_Param_Of_Access_Subp_Wrapper (Formal)
         then
            N := N + 1;
         end if;
         Einfo.Utils.Next_Formal (Formal);
      end loop;

      return N;
   end Number_Formals;

   -----------------
   -- Object_Size --
   -----------------

   function Object_Size (Typ : Type_Kind_Id) return Uint is
     (Einfo.Entities.Esize (Typ));

   --------------------------
   -- Overridden_Operation --
   --------------------------

   function Overridden_Operation
     (E : Subprogram_Kind_Id) return Opt_Subprogram_Kind_Id
   is
      Parent_E : constant Opt_Subprogram_Kind_Id :=
        Einfo.Entities.Overridden_Operation (E);
   begin
      if Present (Parent_E) then
         return Sem_Aux.Ultimate_Alias (Parent_E);
      end if;
      return Empty;
   end Overridden_Operation;

   -------------------------
   -- Package_Body_Entity --
   -------------------------

   function Package_Body_Entity
     (Pack : N_Package_Body_Id)
      return E_Package_Body_Id
   is (Sem_Util.Defining_Entity (Pack));

   ------------------
   -- Package_Body --
   ------------------

   function Package_Body
     (Pack : E_Package_Id)
      return Opt_N_Package_Body_Id
   is (Sem_Aux.Package_Body (Pack));

   ---------------------------
   -- Partial_DIC_Procedure --
   ---------------------------

   function Partial_DIC_Procedure
     (Typ : Type_Kind_Id)
      return Opt_E_Procedure_Id
   is (Einfo.Utils.Partial_DIC_Procedure (Typ));

   ------------------------
   -- Predicate_Function --
   ------------------------

   function Predicate_Function (Typ : Type_Kind_Id) return Opt_E_Function_Id is
     (Einfo.Utils.Predicate_Function (Typ));

   -------------------------------------
   -- Private_Declarations_Of_Package --
   -------------------------------------

   function Private_Declarations_Of_Package
     (Pack : E_Package_Id)
      return List_Id
   is
     (Sinfo.Nodes.Private_Declarations (Sem_Aux.Package_Specification (Pack)));

   -----------------------
   -- Return_Applies_To --
   -----------------------

   function Return_Applies_To (E : E_Return_Statement_Id) return Node_Id is
     (Einfo.Entities.Return_Applies_To (E));

   -----------------------
   -- Stored_Constraint --
   -----------------------

   function Stored_Constraint (Typ : Type_Kind_Id) return Elist_Id is
     (Einfo.Entities.Stored_Constraint (Typ));

   ---------------------
   -- Type_High_Bound --
   ---------------------

   function Type_High_Bound (Typ : Scalar_Kind_Id) return Opt_N_Subexpr_Id is
     (Einfo.Utils.Type_High_Bound (Typ));

   --------------------
   -- Type_Low_Bound --
   --------------------

   function Type_Low_Bound (Typ : Entity_Id) return Opt_N_Subexpr_Id is
     (if Ekind (Typ) = E_String_Literal_Subtype then
           String_Literal_Low_Bound (Typ)
      else Einfo.Utils.Type_Low_Bound (Typ));

   -----------------------
   -- Ultimate_Ancestor --
   -----------------------

   function Ultimate_Ancestor (Typ : Type_Kind_Id) return Type_Kind_Id is
     (Sem_Aux.First_Subtype
       (Einfo.Utils.Root_Type (Einfo.Utils.Base_Type (Typ))));

   -------------------------------------
   -- Visible_Declarations_Of_Package --
   -------------------------------------

   function Visible_Declarations_Of_Package
     (Pack : E_Package_Id)
      return List_Id
   is
     (Sinfo.Nodes.Visible_Declarations
        (Sem_Aux.Package_Specification (Pack)));

end SPARK_Atree.Entities;
