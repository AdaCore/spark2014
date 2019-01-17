------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - I N I T                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                    Copyright (C) 2018-2019, AdaCore                      --
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

with Ada.Containers.Hashed_Maps;
with Common_Containers;        use Common_Containers;
with Namet;                    use Namet;
with SPARK_Atree;              use SPARK_Atree;
with SPARK_Util.Types;         use SPARK_Util.Types;
with VC_Kinds;                 use VC_Kinds;
with Why.Atree.Accessors;      use Why.Atree.Accessors;
with Why.Atree.Builders;       use Why.Atree.Builders;
with Why.Atree.Modules;        use Why.Atree.Modules;
with Why.Gen.Arrays;           use Why.Gen.Arrays;
with Why.Gen.Binders;          use Why.Gen.Binders;
with Why.Gen.Decl;             use Why.Gen.Decl;
with Why.Gen.Expr;             use Why.Gen.Expr;
with Why.Gen.Names;            use Why.Gen.Names;
with Why.Gen.Preds;            use Why.Gen.Preds;
with Why.Gen.Progs;            use Why.Gen.Progs;
with Why.Gen.Records;          use Why.Gen.Records;
with Why.Inter;                use Why.Inter;

package body Why.Gen.Init is

   package Entity_W_Type_Map is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Entity_Id,
        Element_Type    => W_Type_Id,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   Abst_Wrapper_Types  : Entity_W_Type_Map.Map;
   Split_Wrapper_Types : Entity_W_Type_Map.Map;
   --  Maps to store wrapper types. It is used to always return the same type
   --  for a given entity. Also register whether a wrapper is in split form or
   --  not.

   function Is_Split_Wrapper_Type (Typ : W_Type_Id) return Boolean;
   --  Return True if Typ is a wrapper type in split form

   ----------------------------
   -- Compute_Is_Initialized --
   ----------------------------

   function Compute_Is_Initialized
     (E    : Entity_Id;
      Name : W_Term_Id)
      return W_Pred_Id
   is

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id;

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id)
         return W_Pred_Id
      is (Compute_Is_Initialized (E => C_Ty, Name => C_Expr));

      -----------------------------
      -- Is_Initialized_For_Comp --
      -----------------------------

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id
      is
         pragma Unreferenced (E);
      begin
         return Compute_Is_Initialized (E => C_Ty, Name => C_Expr);
      end Is_Initialized_For_Comp;

      function Is_Initialized_For_Array is new Build_Predicate_For_Array
        (Is_Initialized_For_Comp);

      function Is_Initialized_For_Record is new Build_Predicate_For_Record
        (Is_Initialized_For_Comp, Is_Initialized_For_Comp);

      P    : W_Pred_Id := True_Pred;
      Tmp  : constant W_Expr_Id := New_Temp_For_Expr (+Name);
      Expr : W_Expr_Id := Tmp;
   begin
      if Has_Init_By_Proof (E) then

         --  Initialization of top level type

         if Needs_Init_Wrapper_Type (E)
           and then Is_Init_Wrapper_Type (Get_Type (+Name))
         then
            P := Pred_Of_Boolean_Term
              (+New_Init_Attribute_Access (E, +Name));
            Expr := New_Init_Wrapper_Value_Access
              (Ada_Node => Empty,
               E        => E,
               Name     => Expr,
               Domain   => EW_Term);
         end if;

         --  Initialization of components

         if Has_Array_Type (E) then
            P := +New_And_Then_Expr
              (Left   => +P,
               Right  => +Is_Initialized_For_Array (+Expr, Retysp (E)),
               Domain => EW_Pred);
         elsif Has_Record_Type (E) then
            P := +New_And_Then_Expr
              (Left   => +P,
               Right  => +Is_Initialized_For_Record (+Expr, Retysp (E)),
               Domain => EW_Pred);
         end if;

         return +Binding_For_Temp (Domain  => EW_Pred,
                                   Tmp     => Tmp,
                                   Context => +P);
      else
         return True_Pred;
      end if;
   end Compute_Is_Initialized;

   --------------------------
   -- Declare_Init_Wrapper --
   --------------------------

   procedure Declare_Init_Wrapper (P : W_Section_Id; E : Entity_Id) is
      Ty        : constant W_Type_Id := EW_Abstract (E);
      W_Nam     : constant W_Name_Id :=
        To_Local (Get_Name (EW_Init_Wrapper (E, EW_Abstract)));
      W_Ty      : constant W_Type_Id := New_Named_Type (W_Nam);
      Init_Val  : constant W_Identifier_Id :=
        To_Local (E_Symb (E, WNE_Init_Value));
      Attr_Init : constant W_Identifier_Id :=
        To_Local (E_Symb (E, WNE_Attr_Init));

   begin
      --  Add with close for the type that we are wrapping

      if Has_Static_Array_Type (E) then
         Add_With_Clause (P, Get_Array_Theory (E).Module, EW_Clone_Default);
      elsif not Is_Standard_Boolean_Type (E) then
         Add_With_Clause (P, E_Module (E), EW_Clone_Default);
      end if;

      --  Wrappers have two fields, a value field and an initialization flag

      Emit_Record_Declaration
        (Section      => P,
         Name         => W_Nam,
         Binders      =>
           (1 =>
              (B_Name => Init_Val,
               others => <>),
            2 =>
              (B_Name => Attr_Init,
               others => <>)),
         SPARK_Record => True);

      --  Define a program function to access the value field. It checks that
      --  the initialization flag is set.

      declare
         A_Ident  : constant W_Identifier_Id :=
           New_Identifier (Name => "a", Typ => W_Ty);
         A_Binder : constant Binder_Array :=
           (1 => (B_Name => A_Ident,
                  others => <>));
         Pre      : constant W_Pred_Id :=
           Pred_Of_Boolean_Term
             (New_Record_Access (Name  => +A_Ident,
                                 Field => Attr_Init,
                                 Typ   => EW_Bool_Type));
         Post     : constant W_Pred_Id :=
           +New_Comparison
             (Symbol => Why_Eq,
              Left   => +New_Result_Ident (Ty),
              Right  => New_Record_Access (Name  => +A_Ident,
                                           Field => Init_Val,
                                           Typ   => Ty),
              Domain => EW_Pred);

      begin
         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => To_Program_Space (Init_Val),
                  Binders     => A_Binder,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => Ty,
                  Pre         => Pre,
                  Post        => Post));
      end;

   end Declare_Init_Wrapper;

   ---------------------
   -- EW_Init_Wrapper --
   ---------------------

   function EW_Init_Wrapper (E : Entity_Id; K : EW_Type) return W_Type_Id is
      use Entity_W_Type_Map;
      Ty       : constant Entity_Id := Retysp (E);
      C        : Cursor;
      Inserted : Boolean;
   begin
      if K = EW_Abstract then

         --  Create a new type for the wrapper

         if Needs_Init_Wrapper_Type (Ty) then
            Abst_Wrapper_Types.Insert
              (Key      => Ty,
               New_Item => New_Type
                 (Ada_Node   => Ty,
                  Is_Mutable => False,
                  Type_Kind  => EW_Wrapper,
                  Name       => New_Name
                    (Symbol => NID (Short_Name (Ty) & "__init_wrapper"),
                     Module => E_Init_Module (Ty))),
               Inserted => Inserted,
               Position => C);
            return Element (C);
         else
            return EW_Abstract (Ty);
         end if;
      else

         --  No new type is created, this is a placeholder for values

         if Needs_Init_Wrapper_Type (Ty) then
            Split_Wrapper_Types.Insert
              (Key      => Ty,
               New_Item => New_Type
                 (Ada_Node   => Ty,
                  Is_Mutable => False,
                  Type_Kind  => EW_Wrapper,
                  Name       => Get_Name (EW_Split (Ty))),
               Inserted => Inserted,
               Position => C);
            return Element (C);
         else
            return EW_Split (Ty);
         end if;
      end if;
   end EW_Init_Wrapper;

   function EW_Init_Wrapper (Ty : W_Type_Id) return W_Type_Id is
      K : constant EW_Type := Get_Type_Kind (Ty);
   begin
      if K in EW_Abstract | EW_Split then
         return EW_Init_Wrapper (Get_Ada_Node (+Ty), K);
      else
         return Ty;
      end if;
   end EW_Init_Wrapper;

   ---------------------------------
   -- Insert_Initialization_Check --
   ---------------------------------

   function Insert_Initialization_Check
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain)
      return W_Expr_Id
   is
      Tmp : constant W_Identifier_Id := New_Temp_Identifier
        (Typ => Get_Type (Name));
   begin
      if Domain = EW_Prog and then Has_Init_By_Proof (E) then
         return New_Binding
           (Ada_Node => Ada_Node,
            Domain   => EW_Prog,
            Name     => Tmp,
            Def      => Name,
            Context  => +Sequence
              (Ada_Node => Ada_Node,
               Left     => New_Located_Assert
                 (Ada_Node => Ada_Node,
                  Pred     => Compute_Is_Initialized (E, +Tmp),
                  Reason   => VC_Initialization_Check,
                  Kind     => EW_Assert),
               Right    => +Tmp),
            Typ      => Get_Type (Name));
      else
         return Name;
      end if;
   end Insert_Initialization_Check;

   --------------------------
   -- Is_Init_Wrapper_Type --
   --------------------------

   function Is_Init_Wrapper_Type (Typ : W_Type_Id) return Boolean is
   begin
      return Get_Type_Kind (Typ) = EW_Wrapper;
   end Is_Init_Wrapper_Type;

   ---------------------------
   -- Is_Split_Wrapper_Type --
   ---------------------------

   function Is_Split_Wrapper_Type (Typ : W_Type_Id) return Boolean is
   begin
      return Get_Type_Kind (Typ) = EW_Wrapper
        and then Split_Wrapper_Types.Contains (Get_Ada_Node (+Typ))
        and then Typ = Split_Wrapper_Types.Element (Get_Ada_Node (+Typ));
   end Is_Split_Wrapper_Type;

   -------------------------------
   -- New_Init_Attribute_Access --
   -------------------------------

   function New_Init_Attribute_Access
     (E    : Entity_Id;
      Name : W_Expr_Id)
      return W_Expr_Id
   is
      Field : W_Identifier_Id;

   begin
      --  If Name is in split form, use the Symbol_Table to get the init
      --  attribute.

      if Is_Split_Wrapper_Type (Get_Type (Name)) then
         pragma Assert (Get_Type (Name) = EW_Init_Wrapper (E, EW_Split));
         declare
            Ent : constant Item_Type :=
              Ada_Ent_To_Why.Element
                (Symbol_Table,
                 Get_Entity_Of_Variable (Name));
         begin
            if Ent.Init.Present then
               return New_Deref (Right => Ent.Init.Id,
                                 Typ   => EW_Bool_Type);
            else
               return +True_Term;
            end if;
         end;

      --  Otherwise, query the record component

      else
         pragma Assert (Get_Type (Name) = EW_Init_Wrapper (E, EW_Abstract));
         Field := E_Symb (E, WNE_Attr_Init);
         return New_Record_Access (Name   => +Name,
                                   Field  => Field,
                                   Typ    => EW_Bool_Type);
      end if;
   end New_Init_Attribute_Access;

   -----------------------------------
   -- New_Init_Wrapper_Value_Access --
   -----------------------------------

   function New_Init_Wrapper_Value_Access
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain)
      return W_Expr_Id
   is
      Field : W_Identifier_Id;

   begin
      if not Needs_Init_Wrapper_Type (E) then
         return Name;

      --  If Name is in split form, we don't need any actual conversion. We
      --  just change the type of the node using an empty label. We also
      --  introduce an initialization check if Domain = EW_Prog.

      elsif Is_Split_Wrapper_Type (Get_Type (Name)) then
         pragma Assert (Get_Type (Name) = EW_Init_Wrapper (E, EW_Split));
         declare
            Conv : constant W_Expr_Id := New_Label
              (Ada_Node => Ada_Node,
               Domain   => Domain,
               Labels   => Name_Id_Sets.Empty_Set,
               Def      => Name,
               Typ      => EW_Split (E));
         begin
            if Domain = EW_Prog then
               return +Sequence
                 (Ada_Node => Ada_Node,
                  Left     => New_Located_Assert
                    (Ada_Node => Ada_Node,
                     Pred     => Pred_Of_Boolean_Term
                       (+New_Init_Attribute_Access (E, Name)),
                     Reason   => VC_Initialization_Check,
                     Kind     => EW_Assert),
                  Right    => +Conv);
            else
               return Conv;
            end if;
         end;
      end if;

      --  Otherwise, query the record component

      pragma Assert (Get_Type (Name) = EW_Init_Wrapper (E, EW_Abstract));

      Field := E_Symb (E, WNE_Init_Value);

      if Domain = EW_Prog then
         return
           +New_VC_Call
           (Ada_Node => Ada_Node,
            Name     => To_Program_Space (Field),
            Progs    => (1 => +Name),
            Domain   => EW_Prog,
            Reason   => VC_Initialization_Check,
            Typ      => EW_Abstract (E));
      else
         return New_Record_Access (Name  => +Name,
                                   Field => Field,
                                   Typ   => EW_Abstract (E));
      end if;
   end New_Init_Wrapper_Value_Access;

   ------------------------------
   -- Reconstruct_Init_Wrapper --
   ------------------------------

   function Reconstruct_Init_Wrapper
     (Ada_Node  : Node_Id := Empty;
      Ty        : Entity_Id;
      Value     : W_Expr_Id;
      Init_Attr : W_Expr_Id := +True_Term)
      return W_Expr_Id
   is
   begin
      if not Needs_Init_Wrapper_Type (Ty) then
         return Value;
      else
         return New_Record_Aggregate
           (Ada_Node     => Ada_Node,
            Associations =>
              (1 => New_Field_Association
                   (Domain => EW_Term,
                    Field  => E_Symb (Ty, WNE_Init_Value),
                    Value  => Value),
               2 => New_Field_Association
                 (Domain => EW_Term,
                  Field  => E_Symb (Ty, WNE_Attr_Init),
                  Value  => Init_Attr)),
            Typ          => EW_Init_Wrapper (Ty, EW_Abstract));
      end if;
   end Reconstruct_Init_Wrapper;

end Why.Gen.Init;
