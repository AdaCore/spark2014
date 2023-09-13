------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - I N I T                         --
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

with Common_Containers;           use Common_Containers;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with GNATCOLL.Symbols;            use GNATCOLL.Symbols;
with Gnat2Why.Expr;               use Gnat2Why.Expr;
with SPARK_Atree;                 use SPARK_Atree;
with SPARK_Definition;            use SPARK_Definition;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Types;            use SPARK_Util.Types;
with VC_Kinds;                    use VC_Kinds;
with Why.Atree.Builders;          use Why.Atree.Builders;
with Why.Gen.Arrays;              use Why.Gen.Arrays;
with Why.Gen.Binders;             use Why.Gen.Binders;
with Why.Gen.Decl;                use Why.Gen.Decl;
with Why.Gen.Expr;                use Why.Gen.Expr;
with Why.Gen.Names;               use Why.Gen.Names;
with Why.Gen.Progs;               use Why.Gen.Progs;
with Why.Gen.Records;             use Why.Gen.Records;
with Why.Images;                  use Why.Images;
with Why.Inter;                   use Why.Inter;
with Why.Types;                   use Why.Types;

package body Why.Gen.Init is

   ----------------------------
   -- Compute_Is_Initialized --
   ----------------------------

   function Compute_Is_Initialized
     (E                  : Entity_Id;
      Name               : W_Expr_Id;
      Params             : Transformation_Params;
      Domain             : EW_Domain;
      Exclude_Relaxed    : W_Term_Id := False_Term;
      For_Eq             : Boolean := False;
      No_Predicate_Check : Boolean := False;
      Use_Pred           : Boolean := True)
      return W_Expr_Id
   is

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id;
      --  Call Compute_Is_Initialized recursively

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id)
         return W_Pred_Id
      is (Is_Initialized_For_Comp (C_Expr, C_Ty, Empty));

      -----------------------------
      -- Is_Initialized_For_Comp --
      -----------------------------

      function Is_Initialized_For_Comp
        (C_Expr : W_Term_Id; C_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id
      is
      begin
         --  E may be a type standing for the private part of a type whose
         --  fullview is not in SPARK.

         if Present (E) and then Is_Type (E) then
            if Get_Relaxed_Init (Get_Type (+C_Expr)) then
               return +Pred_Of_Boolean_Term
                 (+New_Init_Attribute_Access (E, +C_Expr));
            else
               return True_Pred;
            end if;
         elsif (For_Eq and then not Use_Predefined_Equality_For_Type (C_Ty))
           or else (Is_True_Boolean (+Exclude_Relaxed)
                    and then Has_Relaxed_Init (C_Ty))
         then
            return True_Pred;
         else
            declare
               P : W_Pred_Id := +Compute_Is_Initialized
                 (E               => C_Ty,
                  Name            => +C_Expr,
                  Params          => Params,
                  Domain          => EW_Pred,
                  Exclude_Relaxed => Exclude_Relaxed,
                  For_Eq          => For_Eq);
            begin
               if Has_Relaxed_Init (C_Ty)
                 and then not Is_False_Boolean (+Exclude_Relaxed)
               then
                  P := New_Conditional
                    (Condition => New_Not
                       (Right => Pred_Of_Boolean_Term (Exclude_Relaxed)),
                     Then_Part => P);
               end if;

               return P;
            end;
         end if;
      end Is_Initialized_For_Comp;

      function Is_Initialized_For_Array is new Build_Predicate_For_Array
        (Is_Initialized_For_Comp);

      function Is_Initialized_For_Record is new Build_Predicate_For_Record
        (Is_Initialized_For_Comp, Is_Initialized_For_Comp,
         Ignore_Private_State => False);

      P   : W_Pred_Id;
      R   : W_Expr_Id;
      Tmp : constant W_Expr_Id := New_Temp_For_Expr (+Name);

   --  Start of processing for Compute_Is_Initialized

   begin
      --  An object is necessarily initialized if it does not have a wrapper
      --  type and either it does not have parts which have relaxed
      --  initialization, or we do not need to check subcomponents with relaxed
      --  initialization.

      if not Get_Relaxed_Init (Get_Type (+Name))
        and then (Has_Scalar_Type (E)
                  or else Is_Simple_Private_Type (E)
                  or else Is_True_Boolean (+Exclude_Relaxed)
                  or else not Contains_Relaxed_Init_Parts (E))
      then
         return Bool_True (Domain);

      else

         --  Initialization of types with a top level initialization flag

         if Get_Type (+Name) = M_Boolean_Init_Wrapper.Wrapper_Ty
           or else Has_Scalar_Type (E)
           or else Is_Simple_Private_Type (E)
         then
            R := New_Init_Attribute_Access (E, +Name);

            if Domain = EW_Pred then
               R := +Pred_Of_Boolean_Term (+R);
            end if;

            return R;

         --  For composite types, use the Is_Initialized predicate symbol if
         --  possible.

         elsif Use_Pred
           and then not Is_Itype (E)
           and then Get_Relaxed_Init (Get_Type (+Name))
           and then Get_Type_Kind (Get_Type (+Name)) = EW_Abstract
           and then not No_Predicate_Check
           and then not For_Eq
         then
            P := New_Call (Name => E_Symb (E => E,
                                           S => WNE_Is_Initialized_Pred),
                           Args => (1 => +Tmp, 2 => +Exclude_Relaxed),
                           Typ  => EW_Bool_Type);

         --  Initialization of composite types

         elsif Has_Array_Type (E) then
            P := Is_Initialized_For_Array (+Tmp, Retysp (E));
         elsif Is_Record_Type_In_Why (Retysp (E)) then
            P := Is_Initialized_For_Record (+Tmp, Retysp (E));
         else
            raise Program_Error;
         end if;

         --  If Expr has an init wrapper type, add the predicate if any

         if not No_Predicate_Check
           and then Is_Init_Wrapper_Type (Get_Type (+Tmp))
         then
            declare
               Typ_Pred     : constant W_Pred_Id :=
                 Compute_Dynamic_Predicate
                   (Insert_Simple_Conversion
                      (Expr => +Tmp, To => EW_Abstract (Retysp (E))),
                    Retysp (E), Params);
               --  Don't use the wrapper type to avoid duplicating the
               --  initialization checks already performed.

            begin
               if not Is_True_Boolean (+Typ_Pred) then
                  P := New_And_Pred (Left  => P,
                                     Right => Typ_Pred);
               end if;
            end;
         end if;

         R := Boolean_Expr_Of_Pred
           (W      => +P,
            Domain => Domain);

         if not Is_True_Boolean (+P) then
            R := Binding_For_Temp (Domain  => Domain,
                                   Tmp     => Tmp,
                                   Context => R);
         end if;

         return R;
      end if;
   end Compute_Is_Initialized;

   --------------------------
   -- Declare_Init_Wrapper --
   --------------------------

   procedure Declare_Init_Wrapper (Th : Theory_UC; E : Entity_Id) is
   begin
      if Is_Scalar_Type (E) then
         Declare_Simple_Wrapper_Type
           (Th           => Th,
            W_Nam        => To_Why_Type
              (E, Local => True, Relaxed_Init => True),
            Init_Val     => To_Local (E_Symb (E, WNE_Init_Value)),
            Attr_Init    => To_Local (E_Symb (E, WNE_Attr_Init)),
            Of_Wrapper   => To_Local (E_Symb (E, WNE_Of_Wrapper)),
            To_Wrapper   => To_Local (E_Symb (E, WNE_To_Wrapper)),
            Dummy        => To_Local (E_Symb (E, WNE_Dummy)),
            Default_Init =>
              Default_Initialization (E) = Full_Default_Initialization);
      elsif Is_Record_Type_In_Why (E) then
         Declare_Init_Wrapper_For_Record (Th, E);
      elsif Is_Array_Type (E) then
         Declare_Init_Wrapper_For_Array (Th, E);
      else
         raise Program_Error;
      end if;
   end Declare_Init_Wrapper;

   ---------------------------------
   -- Declare_Simple_Wrapper_Type --
   ---------------------------------

   procedure Declare_Simple_Wrapper_Type
     (Th           : Theory_UC;
      W_Nam        : W_Name_Id;
      Init_Val     : W_Identifier_Id;
      Attr_Init    : W_Identifier_Id;
      Of_Wrapper   : W_Identifier_Id;
      To_Wrapper   : W_Identifier_Id;
      Dummy        : W_Identifier_Id;
      Default_Init : Boolean)
   is
      W_Ty      : constant W_Type_Id := New_Named_Type (W_Nam);
      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => W_Ty);
      A_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));
      X_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "x", Typ => Get_Typ (Init_Val));
      X_Binder  : constant Binder_Array :=
        (1 => (B_Name => X_Ident,
               others => <>));

   begin
      --  Wrappers have two fields, a value field and an initialization
      --  flag.

      Emit_Record_Declaration
        (Th      => Th,
         Name    => W_Nam,
         Binders =>
           (1 =>
                (B_Name => Init_Val,
                 Labels => Get_Model_Trace_Label ("'" & Init_Val_Label),
                 others => <>),
            2 =>
              (B_Name   => Attr_Init,
               Labels   => Get_Model_Trace_Label ("'" & Initialized_Label),
               others   => <>)));

      --  Declare conversion functions to and from the wrapper type

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Of_Wrapper,
            Binders     => A_Binder,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Get_Typ (Init_Val),
            Def         => New_Record_Access (Name  => +A_Ident,
                                              Field => Init_Val,
                                              Typ   => Get_Typ (Init_Val))));
      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Wrapper,
            Binders     => X_Binder,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => W_Ty,
            Def         =>
              New_Record_Aggregate
                (Associations =>
                     (1 => New_Field_Association
                        (Domain => EW_Term,
                         Field  => Init_Val,
                         Value  => +X_Ident),
                      2 => New_Field_Association
                        (Domain => EW_Term,
                         Field  => Attr_Init,
                         Value  => +True_Term)))));
      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Dummy,
            Binders     => Binder_Array'(1 .. 0 => <>),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => W_Ty));
      Emit
        (Th,
         New_Axiom
           (Ada_Node => Empty,
            Name     => NID (Img (Get_Symb (Get_Name (Dummy))) & "__def"),
            Def      => New_Comparison
              (Symbol => Why_Eq,
               Left   => New_Record_Access
                 (Field => Attr_Init,
                  Name  => +Dummy,
                  Typ   => EW_Bool_Type),
               Right  => (if Default_Init then True_Term else False_Term)),
            Dep       =>
              New_Axiom_Dep (Name => Dummy, Kind => EW_Axdep_Func)));
   end Declare_Simple_Wrapper_Type;

   ---------------------
   -- EW_Init_Wrapper --
   ---------------------

   function EW_Init_Wrapper (Ty : W_Type_Id) return W_Type_Id is
   begin
      case Get_Type_Kind (Ty) is
         when EW_Abstract =>
            return EW_Abstract (Get_Ada_Node (+Ty), Relaxed_Init => True);
         when EW_Split =>
            return EW_Split (Get_Ada_Node (+Ty), Relaxed_Init => True);
         when EW_Builtin =>
            pragma Assert (Ty = EW_Bool_Type);
            return M_Boolean_Init_Wrapper.Wrapper_Ty;
      end case;
   end EW_Init_Wrapper;

   -----------------------------
   -- Get_Init_Id_From_Object --
   -----------------------------

   function Get_Init_Id_From_Object
     (Obj         : Entity_Id;
      Ref_Allowed : Boolean) return W_Expr_Id
   is
      C    : constant Ada_Ent_To_Why.Cursor :=
        Ada_Ent_To_Why.Find (Symbol_Table, Obj);
      Item : Item_Type;
   begin
      if Ada_Ent_To_Why.Has_Element (C) then
         Item := Ada_Ent_To_Why.Element (C);
         if Item.Init.Present then
            if Ref_Allowed then
               return New_Deref
                 (Right => Item.Init.Id,
                  Typ   => Get_Typ (Item.Init.Id));
            else
               return +Item.Init.Id;
            end if;
         end if;
      end if;
      return Why_Empty;
   end Get_Init_Id_From_Object;

   ---------------------------------
   -- Insert_Initialization_Check --
   ---------------------------------

   function Insert_Initialization_Check
     (Ada_Node           : Node_Id;
      E                  : Entity_Id;
      Name               : W_Expr_Id;
      Domain             : EW_Domain;
      Exclude_Relaxed    : Boolean := False;
      For_Eq             : Boolean := False;
      No_Predicate_Check : Boolean := False)
      return W_Expr_Id
   is
      Tmp : constant W_Expr_Id := New_Temp_For_Expr (Name);
      T   : W_Expr_Id;
   begin
      --  We need initialization checking if either Name is an expression with
      --  relaxed initialization or if it contains subcomponents with
      --  relaxed initialization and checks should be introduced for
      --  these subcomponents (Excluded_Subcomponents is not Relaxed).

      if Domain = EW_Prog
        and then
          (Is_Init_Wrapper_Type (Get_Type (Name))
           or else
             (not Exclude_Relaxed
              and then Contains_Relaxed_Init_Parts (E, Ignore_Top => True)))
      then
         T := +Sequence
              (Ada_Node => Get_Ada_Node (+Tmp),
               Left     => New_Located_Assert
                 (Ada_Node => Ada_Node,
                  Pred     => +Compute_Is_Initialized
                    (E, +Tmp,
                     Params             => Body_Params,
                     Exclude_Relaxed =>
                       (if Exclude_Relaxed then True_Term else False_Term),
                     For_Eq             => For_Eq,
                     No_Predicate_Check => No_Predicate_Check,
                     Domain             => EW_Pred),
                  Reason   => VC_Initialization_Check,
                  Kind     => EW_Assert),
               Right    => +Tmp);
         T := Binding_For_Temp (Ada_Node => Get_Ada_Node (+Tmp),
                                Domain   => Domain,
                                Tmp      => Tmp,
                                Context  => T);
         return T;
      else
         return Name;
      end if;
   end Insert_Initialization_Check;

   --------------------------
   -- Is_Init_Wrapper_Type --
   --------------------------

   function Is_Init_Wrapper_Type (Typ : W_Type_Id) return Boolean is
   begin
      return Get_Relaxed_Init (Typ);
   end Is_Init_Wrapper_Type;

   -------------------------------
   -- New_Init_Attribute_Access --
   -------------------------------

   function New_Init_Attribute_Access
     (E    : Entity_Id;
      Name : W_Expr_Id) return W_Expr_Id
   is
      Field : W_Identifier_Id;

   begin
      pragma Assert (Get_Relaxed_Init (Get_Type (Name)));

      --  Name is necessarily in abstract form. Query the record component.
      --  In general, the name of the attribute is declared in the type's
      --  module.

      if Get_Type_Kind (Get_Type (Name)) = EW_Abstract then
         Field := E_Symb (E, WNE_Attr_Init);

      --  For standard boolean, it is in the boolean init wrapper module

      else
         pragma Assert (Get_Type (Name) = M_Boolean_Init_Wrapper.Wrapper_Ty);
         Field := M_Boolean_Init_Wrapper.Attr_Init;
      end if;

      return New_Record_Access (Name   => +Name,
                                Field  => Field,
                                Typ    => EW_Bool_Type);
   end New_Init_Attribute_Access;

end Why.Gen.Init;
