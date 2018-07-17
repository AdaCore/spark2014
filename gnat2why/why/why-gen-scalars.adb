------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2018, AdaCore                   --
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

with Common_Containers;   use Common_Containers;
with GNAT.Source_Info;
with SPARK_Util;          use SPARK_Util;
with SPARK_Util.Types;    use SPARK_Util.Types;
with Sinput;              use Sinput;
with Stand;               use Stand;
with Uintp;               use Uintp;
with Urealp;              use Urealp;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Ids;             use Why.Ids;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

package body Why.Gen.Scalars is

   procedure Create_Fixed_Point_Theory_If_Needed
     (Current_File : W_Section_Id;
      Typ          : Entity_Id);
   --  Create a theory for fixed point operation with the small of Typ. Only
   --  one such theory is created for each value of small. The symbols for
   --  these theories are stored in the M_Fixed_Points map.

   procedure Define_Scalar_Attributes
     (Section    : W_Section_Id;
      E          : Entity_Id;
      Base_Type  : W_Type_Id);
   --  Define the attributes first, last, modulus, small for the given type.

   function Num_Constant (Ty : Entity_Id; N : Node_Id) return W_Term_Id;
   --  N must be a value whose value is known at compile time. This function
   --  evaluates N as an Uint (if Ty is a discrete type or a fixed-point type)
   --  or as real (if Ty is not discrete).

   function Ureal_Name (R : Ureal) return String is
     (UI_Image (Norm_Num (R), Decimal) & "_" &
        UI_Image (Norm_Den (R), Decimal));
   --  Compute a name from a Ureal

   -----------------------------------------
   -- Create_Fixed_Point_Theory_If_Needed --
   -----------------------------------------

   procedure Create_Fixed_Point_Theory_If_Needed
     (Current_File : W_Section_Id;
      Typ          : Entity_Id)
   is
      use Name_Id_Fixed_Point_Map;

      File        : constant W_Section_Id := WF_Pure;
      Module_Name : constant Name_Id :=
        Get_Fixed_Point_Theory_Name (Typ => Typ);
      Module      : constant W_Module_Id :=
        New_Module (File => No_Name,
                    Name => Module_Name);
      N_Ty        : constant W_Type_Id := New_Type
        (Ada_Node   => Base_Retysp (Typ),
         Is_Mutable => False,
         Type_Kind  => EW_Builtin,
         Name       => Get_Name (M_Main.Fixed_Type));
      M_Module    : constant M_Fixed_Point_Type :=
        M_Fixed_Point_Type'
          (Module      => Module,
           T           => N_Ty,
           Mult_Int    =>
             New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => NID ("fxp_mult_int"),
                             Typ    => N_Ty),
           Div_Int     =>
             New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => NID ("fxp_div_int"),
                             Typ    => N_Ty),
           Div_Int_Res =>
             New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => NID ("fxp_div_result_int"),
                             Typ    => EW_Int_Type),
           Of_Int      =>
             New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => NID ("of_int"),
                             Typ    => N_Ty),
           To_Int      =>
             New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => NID ("to_int"),
                             Typ    => EW_Int_Type));

      Num_Small : constant W_Name_Id :=
        New_Name (Symbol => NID ("num_small"));
      Den_Small : constant W_Name_Id :=
        New_Name (Symbol => NID ("den_small"));

      Small       : constant Ureal := Small_Value (Typ);
      Num_Small_V : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Num (Small));
      Den_Small_V : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Den (Small));

      Subst : W_Clone_Substitution_Array (1 .. 2);

      Save_Theory : W_Theory_Declaration_Id;
      --  Use this variable to temporarily store current theory

   begin
      --  If there is already a module for that value of small, there is
      --  nothing to do.

      if M_Fixed_Points.Contains (Module_Name) then
         return;
      end if;

      --  Temporarily store the current theory if needed

      if File = Current_File then
         Save_Theory := Why_Sections (File).Cur_Theory;
         Why_Sections (File).Cur_Theory := Why_Empty;
      end if;

      Open_Theory
        (File, Module,
         Comment =>
           "Module for fixed-point operation for type at "
         & Build_Location_String (Sloc (Typ))
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Num_Small),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Num_Small_V));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Den_Small),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Den_Small_V));

      Subst :=
        (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Num_Small,
                 Image     => Num_Small),
         2 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Den_Small,
                 Image     => Den_Small));

      Emit (File,
            New_Clone_Declaration
              (Theory_Kind   => EW_Theory,
               Clone_Kind    => EW_Export,
               Origin        => Fixed_Point_Rep,
               As_Name       => No_Name,
               Substitutions => Subst));

      Close_Theory (File, Kind => Definition_Theory);

      --  Restore the current theory

      if File = Current_File then
         Why_Sections (File).Cur_Theory := Save_Theory;
      end if;

      M_Fixed_Points.Insert (Module_Name, M_Module);
   end Create_Fixed_Point_Theory_If_Needed;

   --------------------------------------------------
   -- Create_Fixed_Point_Mult_Div_Theory_If_Needed --
   --------------------------------------------------

   procedure Create_Fixed_Point_Mult_Div_Theory_If_Needed
     (Current_File : W_Section_Id;
      Typ_Left     : Entity_Id;
      Typ_Right    : Entity_Id;
      Typ_Result   : Entity_Id;
      Expr         : Node_Id)
   is
      use Name_Id_Fixed_Point_Mult_Div_Map;

      File        : constant W_Section_Id := WF_Pure;
      Module_Name : constant Name_Id :=
        Get_Fixed_Point_Mult_Div_Theory_Name (Typ_Left   => Typ_Left,
                                              Typ_Right  => Typ_Right,
                                              Typ_Result => Typ_Result);
      Module      : constant W_Module_Id :=
        New_Module (File => No_Name,
                    Name => Module_Name);
      M_Module    : constant M_Fixed_Point_Mult_Div_Type :=
        M_Fixed_Point_Mult_Div_Type'
          (Module => Module,
           Mult   => New_Identifier (Module => Module,
                                     Domain => EW_Term,
                                     Symbol => NID ("fxp_mult"),
                                     Typ    => Base_Why_Type (Typ_Result)),
           Div    => New_Identifier (Module => Module,
                                     Domain => EW_Term,
                                     Symbol => NID ("fxp_div"),
                                     Typ    => Base_Why_Type (Typ_Result)));

      Num_Small_X : constant W_Name_Id :=
        New_Name (Symbol => NID ("num_small_x"));
      Den_Small_X : constant W_Name_Id :=
        New_Name (Symbol => NID ("den_small_x"));
      Num_Small_Y : constant W_Name_Id :=
        New_Name (Symbol => NID ("num_small_y"));
      Den_Small_Y : constant W_Name_Id :=
        New_Name (Symbol => NID ("den_small_y"));
      Num_Small_Res : constant W_Name_Id :=
        New_Name (Symbol => NID ("num_small_res"));
      Den_Small_Res : constant W_Name_Id :=
        New_Name (Symbol => NID ("den_small_res"));

      Small_L      : constant Ureal := Small_Value (Typ_Left);
      Num_Small_L   : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Num (Small_L));
      Den_Small_L : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Den (Small_L));

      Small_R       : constant Ureal :=
        (if Has_Fixed_Point_Type (Typ_Right) then
           Small_Value (Typ_Right)
         elsif Has_Signed_Integer_Type (Typ_Right) then
           Ureal_1
         else raise Program_Error);
      Num_Small_R   : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Num (Small_R));
      Den_Small_R : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Den (Small_R));

      Small_Op       : constant Ureal := Small_Value (Typ_Result);
      Num_Small_Op   : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Num (Small_Op));
      Den_Small_Op : constant W_Term_OId :=
        New_Integer_Constant (Value => Norm_Den (Small_Op));

      Subst : W_Clone_Substitution_Array (1 .. 6);

      Save_Theory : W_Theory_Declaration_Id;
      --  Use this variable to temporarily store current theory

   begin
      --  If there is a already a module for that combination of values of
      --  smalls, there is nothing to do.

      if M_Fixed_Point_Mult_Div.Contains (Module_Name) then
         return;
      end if;

      --  Temporarily store the current theory if needed

      if File = Current_File then
         Save_Theory := Why_Sections (File).Cur_Theory;
         Why_Sections (File).Cur_Theory := Why_Empty;
      end if;

      Open_Theory
        (File, Module,
         Comment =>
           "Module for fixed-point multiplication and division for operation"
         & " at " & Build_Location_String (Sloc (Expr))
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Num_Small_X),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Num_Small_L));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Den_Small_X),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Den_Small_L));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Num_Small_Y),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Num_Small_R));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Den_Small_Y),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Den_Small_R));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Num_Small_Res),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Num_Small_Op));
      Emit (File,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Den_Small_Res),
               Binders     => (1 .. 0 => <>),
               Return_Type => EW_Int_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Location    => No_Location,
               Def         => +Den_Small_Op));

      Subst :=
        (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Num_Small_X,
                 Image     => Num_Small_X),
         2 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Den_Small_X,
                 Image     => Den_Small_X),
         3 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Num_Small_Y,
                 Image     => Num_Small_Y),
         4 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Den_Small_Y,
                 Image     => Den_Small_Y),
         5 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Num_Small_Res,
                 Image     => Num_Small_Res),
         6 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Den_Small_Res,
                 Image     => Den_Small_Res));

      Emit (File,
            New_Clone_Declaration
              (Theory_Kind   => EW_Theory,
               Clone_Kind    => EW_Export,
               Origin        => Fixed_Point_Mult_Div,
               As_Name       => No_Name,
               Substitutions => Subst));

      Close_Theory (File, Kind => Definition_Theory);

      --  Restore the current theory

      if File = Current_File then
         Why_Sections (File).Cur_Theory := Save_Theory;
      end if;

      M_Fixed_Point_Mult_Div.Insert (Module_Name, M_Module);
   end Create_Fixed_Point_Mult_Div_Theory_If_Needed;

   -------------------------
   -- Declare_Scalar_Type --
   -------------------------

   procedure Declare_Scalar_Type
     (File : W_Section_Id;
      E      : Entity_Id)
   is
      Why_Name         : constant W_Name_Id := To_Why_Type (E, Local => True);
      Is_Static        : constant Boolean := not Type_Is_Modeled_As_Base (E);
      Base_Type_In_Why : constant W_Type_Id := EW_Abstract (Base_Type (E));

      function Pick_Clone return W_Module_Id;
      --  Choose the correct module to clone

      function Compute_Clone_Subst return W_Clone_Substitution_Array;
      --  generate the substitutions to be passed to the clone

      procedure Generate_Range_Predicate
        (Ty : W_Type_Id := Base_Why_Type (E);
         Name : Why_Name_Enum);
      --  generate the range predicate for the type. In simple cases, this
      --  predicate simply expresses "first < x < last"

      -------------------------
      -- Compute_Clone_Subst --
      -------------------------

      function Compute_Clone_Subst return W_Clone_Substitution_Array is
         Default_Clone_Subst : constant W_Clone_Substitution_Id :=
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Name (Symbol => NID ("t")),
              Image     => Why_Name);
         Rep_Type_Clone_Substitution : constant W_Clone_Substitution_Array :=
           (if not Is_Static
            and then (Has_Discrete_Type (E)
              or else Has_Floating_Point_Type (E)) then
              (1 => New_Clone_Substitution
               (Kind      => EW_Type_Subst,
                Orig_Name => New_Name
                  (Symbol => NID ("rep_type")),
                Image     => Get_Name (Base_Why_Type (E))))
            else (1 .. 0 => <>));
         Static_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Static then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Local (E_Symb (E, WNE_Attr_First)),
                    Image     => To_Local (E_Symb (E, WNE_Attr_First))),
               2 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Local (E_Symb (E, WNE_Attr_Last)),
                  Image     => To_Local (E_Symb (E, WNE_Attr_Last))),
               3 => New_Clone_Substitution
                 (Kind      => EW_Predicate,
                  Orig_Name => To_Local (E_Symb (E, WNE_Range_Pred)),
                  Image     => To_Local (E_Symb (E, WNE_Range_Pred))))
            else (1 .. 0 => <>));
         Dynamic_Conv_Subst : constant W_Clone_Substitution_Array :=
           (if not Is_Static then
              (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID ("base_to_rep")),
                 Image     =>
                   Get_Name
                     (Conversion_Name
                        (From => Base_Type_In_Why,
                         To   => Base_Why_Type (E)))),
               2 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID ("base_of_rep")),
                 Image     =>
                   Get_Name
                     (Conversion_Name
                        (From => Base_Why_Type (E),
                         To   => Base_Type_In_Why))),
               3 => New_Clone_Substitution
                 (Kind      => EW_Predicate,
                  Orig_Name => To_Local (E_Symb (E, WNE_Dynamic_Property)),
                  Image     => To_Local (E_Symb (E, WNE_Dynamic_Property))))
            else (1 .. 0 => <>));
         Mod_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Static
              and then Has_Modular_Integer_Type (E)
              and then Modulus (E) /= UI_Expon (2, Modular_Size (E))
            then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Local (E_Symb (E, WNE_Attr_Modulus)),
                  Image     => To_Local (E_Symb (E, WNE_Attr_Modulus))))
            else (1 .. 0 => <>));
         Range_Int_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Has_Modular_Integer_Type (E) then
                (if Is_Static then
                     (1 => New_Clone_Substitution
                      (Kind      => EW_Predicate,
                       Orig_Name =>
                         To_Local (E_Symb (E, WNE_Range_Pred_BV_Int)),
                       Image     =>
                         To_Local (E_Symb (E, WNE_Range_Pred_BV_Int))))
                 else
                     (1 => New_Clone_Substitution
                      (Kind      => EW_Predicate,
                       Orig_Name =>
                         To_Local (E_Symb (E, WNE_Dynamic_Property_BV_Int)),
                       Image     =>
                         To_Local (E_Symb (E, WNE_Dynamic_Property_BV_Int)))))
            else (1 .. 0 => <>));
      begin

         return
           Default_Clone_Subst &
           Rep_Type_Clone_Substitution &
           Static_Clone_Subst &
           Dynamic_Conv_Subst &
           Mod_Clone_Subst &
           Range_Int_Clone_Subst;
      end Compute_Clone_Subst;

      ------------------------------
      -- Generate_Range_Predicate --
      ------------------------------

      procedure Generate_Range_Predicate
        (Ty : W_Type_Id := Base_Why_Type (E);
         Name : Why_Name_Enum)
      is
         Var : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => Ty);
         Def : W_Pred_Id := True_Pred;

         --  the names of fst and last must be "first_int/last_int" in the case
         --  where we deal with a modular type and the base type is "int", and
         --  should be simply "first/last" in the case of a static type. In
         --  the dynamic case, we don't care about the name, because we bind
         --  it directly above, so we pick "first_int/last_int" too.

         Fst : constant W_Identifier_Id :=
           (if not Is_Static or else
              (Has_Modular_Integer_Type (E) and then Ty = EW_Int_Type)
            then
               New_Identifier
              (Symbol => NID ("first_int"),
               Domain => EW_Term,
               Typ    => Ty)
            else To_Local (E_Symb (E, WNE_Attr_First)));
         Lst : constant W_Identifier_Id :=
           (if not Is_Static or else
              (Has_Modular_Integer_Type (E) and then Ty = EW_Int_Type)
            then
               New_Identifier
              (Symbol => NID ("last_int"),
               Domain => EW_Term,
               Typ    => Ty)
            else To_Local (E_Symb (E, WNE_Attr_Last)));

      begin
         --  Optimisation:
         --  check if E is (equivalent to) Unsigned_8/16/..
         if Is_Static
           and then Has_Modular_Integer_Type (E)
           and then
             ((Ty = EW_BitVector_8_Type
               and then Modulus (E) = UI_Expon (Uint_2, Uint_8))
              or else
                (Ty = EW_BitVector_16_Type
                 and then Modulus (E)
                        = UI_Expon (Uint_2, Uint_16))
              or else
                (Ty = EW_BitVector_32_Type
                 and then Modulus (E)
                        = UI_Expon (Uint_2, Uint_32))
              or else
                (Ty = EW_BitVector_64_Type
                 and then Modulus (E)
                        = UI_Expon (Uint_2, Uint_64)))
           and then Intval (Type_Low_Bound (E)) = Uint_0
           and then Intval (Type_High_Bound (E))
                  = UI_Sub (Modulus (E), Uint_1)
         then

            --  In which case we know that all values are necessary in range,
            --  So we define the range predicate as always true.
            Emit (File,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain   => EW_Pred,
                     Name     => To_Local (E_Symb (E, Name)),
                     Def      => +True_Pred,
                     Location => No_Location,
                     Labels   => Name_Id_Sets.Empty_Set,
                     Binders  => (1 => Binder_Type'(B_Name => Var,
                                                    others => <>))));

            --  And we directly use the function uint_in_range from the
            --  underlying why3 theory for checking the range againts integers
            --  instead of generating it.
            Emit (File,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain   => EW_Pred,
                     Name     => To_Local (E_Symb (E, WNE_Range_Pred_BV_Int)),
                     Def      => +New_Identifier (Name   => "uint_in_range x",
                                                  Module =>
                                                    MF_BVs
                                                      (Base_Why_Type (E))
                                                  .Module),
                     Location => No_Location,
                     Labels   => Name_Id_Sets.Empty_Set,
                     Binders  => (1 => Binder_Type'
                                      (B_Name => New_Identifier (
                                       Name => "x", Typ => EW_Int_Type),
                                       others => <>))));

            return;
         elsif Has_Floating_Point_Type (E)
         then
            --  Optimisation for static floating point, check if we are dealing
            --  with a Float32 or Float64, in which case reduce the range
            --  predicate to "is_finite".

            if Is_Static
              and then UR_Eq (Expr_Value_R (Type_Low_Bound (E)),
                              Expr_Value_R (Type_Low_Bound
                                (if Ty = EW_Float_32_Type
                                     then Standard_Float
                                     else Standard_Long_Float)))
              and then UR_Eq (Expr_Value_R (Type_High_Bound (E)),
                              Expr_Value_R (Type_High_Bound
                                (if Ty = EW_Float_32_Type
                                     then Standard_Float
                                     else Standard_Long_Float)))
            then

               --  In which case we know that all values are necessary in range
               --  so we define the range predicate as "is_finite".
               Emit (File,
                     Why.Gen.Binders.New_Function_Decl
                       (Domain   => EW_Pred,
                        Name     => To_Local (E_Symb (E, Name)),
                        Def      => New_Call (Domain => EW_Pred,
                                              Name   =>
                                                MF_Floats (Ty).Is_Finite,
                                              Args   => (1 => +Var)),
                        Location => No_Location,
                        Labels   => Name_Id_Sets.Empty_Set,
                        Binders  => (1 => Binder_Type'(B_Name => Var,
                                                       others => <>))));

               return;

            --  In the other case, add "is_finite" to the predicate
            else
               Def := +W_Connection_Id'(New_Connection
                 (Op     => EW_And_Then,
                  Left   => New_Call (Domain => EW_Pred,
                                      Name   =>
                                        MF_Floats (Ty).Is_Finite,
                                      Args   => (1 => +Var)),
                  Right  => +New_Range_Expr (Domain => EW_Pred,
                                             Low    => +Fst,
                                             High   => +Lst,
                                             Expr   => +Var),
                  Domain => EW_Pred));
            end if;
         else

            --  Else, express the range constraints
            Def := +New_And_Expr (Domain => EW_Pred,
                                  Left   => +Def,
                                  Right  =>
                                    +New_Range_Expr (Domain => EW_Pred,
                                                     Low    => +Fst,
                                                     High   => +Lst,
                                                     Expr   => +Var));
         end if;

         --  Emit range predicate if the type is static, a dynamic_property
         --  otherwise.

         declare
            Static_Binders : constant Binder_Array :=
              Binder_Array'(1 => Binder_Type'(B_Name => Var,
                                              others => <>));
            Binders        : constant Binder_Array :=
              (if Is_Static then Static_Binders
               else Binder_Array'(1 => Binder_Type'(B_Name => Fst,
                                                    others => <>),
                                  2 => Binder_Type'(B_Name => Lst,
                                                    others => <>))
               & Static_Binders);
         begin
            Emit (File,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain   => EW_Pred,
                     Name     => To_Local (E_Symb (E, Name)),
                     Def      => +Def,
                     Location => No_Location,
                     Labels   => Name_Id_Sets.Empty_Set,
                     Binders  => Binders));

            --  in case we're dealing with bitvectors, we also need to generate
            --  a range check from integers
            if Why_Type_Is_BitVector (Ty) then
               Generate_Range_Predicate (EW_Int_Type,
                                         (if Is_Static
                                          then WNE_Range_Pred_BV_Int
                                          else WNE_Dynamic_Property_BV_Int));
            end if;
         end;
      end Generate_Range_Predicate;

      ----------------
      -- Pick_Clone --
      ----------------

      function Pick_Clone return W_Module_Id is
         Typ : constant W_Type_Id := Base_Why_Type (E);
      begin
         if Is_Static then
            if Has_Modular_Integer_Type (E) then
               declare
                  Modulus_Val : constant Uint := Modulus (E);
               begin
                  return (if Typ = EW_BitVector_8_Type then
                            (if UI_Lt (Modulus_Val, UI_Expon (2, 8)) then
                                  Static_Modular_lt8
                             else
                                Static_Modular_8)
                          elsif Typ = EW_BitVector_16_Type then
                            (if UI_Lt (Modulus_Val, UI_Expon (2, 16)) then
                                  Static_Modular_lt16
                             else
                                Static_Modular_16)
                          elsif Typ = EW_BitVector_32_Type then
                            (if UI_Lt (Modulus_Val, UI_Expon (2, 32)) then
                                  Static_Modular_lt32
                             else
                                Static_Modular_32)
                          elsif Typ = EW_BitVector_64_Type then
                            (if UI_Lt (Modulus_Val, UI_Expon (2, 64)) then
                                  Static_Modular_lt64
                             else
                                Static_Modular_64)
                          else
                             raise Program_Error);
               end;
            elsif Has_Discrete_Type (E) then
               return Static_Discrete;
            elsif Has_Fixed_Point_Type (E) then
               return Static_Fixed_Point;
            else
               pragma Assert (Has_Floating_Point_Type (E));
               return (if Typ = EW_Float_32_Type then
                          Static_Float32
                       else Static_Float64);
            end if;
         else
            if Has_Modular_Integer_Type (E) then
               return Dynamic_Modular;
            elsif Has_Discrete_Type (E) then
               return Dynamic_Discrete;
            elsif Has_Fixed_Point_Type (E) then
               return Dynamic_Fixed_Point;
            else
               pragma Assert (Has_Floating_Point_Type (E));
               return Dynamic_Float;
            end if;
         end if;
      end Pick_Clone;

      --  Local variables

      Rng                       : constant Node_Id := Get_Range (E);

   --  Start of processing for Declare_Scalar_Type

   begin
      --  Create a theory for the underlying fixed point type if needed

      if Has_Fixed_Point_Type (E) then
         Create_Fixed_Point_Theory_If_Needed (Current_File => File,
                                              Typ          => E);
      end if;

      --  Declare the logic type:
      --  If the type is dynamic, declare an alias of its base type.

      if not Is_Static then
         Emit (File,
               New_Type_Decl
                 (Name  => Why_Name,
                  Alias => Base_Type_In_Why));

      --  For static signed integer types, declare a range type

      elsif Is_Range_Type_In_Why (E) then
         Emit (File,
               New_Type_Decl
                 (Name       => Why_Name,
                  Labels     => Name_Id_Sets.Empty_Set,
                  Definition => New_Range_Type_Definition
                    (First => Expr_Value (Low_Bound (Rng)),
                     Last  => Expr_Value (High_Bound (Rng)))));

      --  For other static types, declare an abstract type

      else
         Emit (File,
               New_Type_Decl
                 (Name   => Why_Name,
                  Labels => Name_Id_Sets.Empty_Set));
      end if;

      --  retrieve and declare the attributes first, last, small, and modulus

      Define_Scalar_Attributes
        (Section    => File,
         E         => E,
         Base_Type => Base_Why_Type (E));

      --  define first_int and last_int for static modular types

      if Is_Static and then Is_Modular_Integer_Type (E) then
         Emit (File,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => New_Identifier
                    (Name => "first_int",
                     Typ  => EW_Int_Type),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => EW_Int_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Location    => No_Location,
                  Def         => New_Integer_Constant
                    (Value => Expr_Value (Low_Bound (Rng)))));
         Emit (File,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => New_Identifier
                    (Name => "last_int",
                     Typ  => EW_Int_Type),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => EW_Int_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Location    => No_Location,
                  Def         => New_Integer_Constant
                    (Value => Expr_Value (High_Bound (Rng)))));
      end if;

      Generate_Range_Predicate (Name => (if Is_Static
                                         then WNE_Range_Pred
                                         else WNE_Dynamic_Property));

      --  clone the appropriate module

      Emit (File,
            New_Clone_Declaration (Theory_Kind   => EW_Module,
                                   Clone_Kind    => EW_Export,
                                   As_Name       => No_Name,
                                   Origin        => Pick_Clone,
                                   Substitutions => Compute_Clone_Subst));
   end Declare_Scalar_Type;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (Section    : W_Section_Id;
      E          : Entity_Id;
      Base_Type  : W_Type_Id)
   is
      Rng  : constant Node_Id := Get_Range (E);
      Low  : constant Node_Id := Low_Bound (Rng);
      High : constant Node_Id := High_Bound (Rng);

      First : constant W_Term_OId :=
        (if Compile_Time_Known_Value (Low)
         then +Num_Constant (E, Low)
         else Why_Empty);

      Last : constant W_Term_OId :=
        (if Compile_Time_Known_Value (High)
         then +Num_Constant (E, High)
         else Why_Empty);

   begin
      --  Compute and declare the modulus attribute of modular integer types

      if Has_Modular_Integer_Type (E) then
         declare
            Modulus_Val : constant Uint := Modulus (E);
            Typ         : constant W_Type_Id := Base_Why_Type (E);
            Modul       : W_Term_OId;
         begin
            Modul := (if Typ = EW_BitVector_8_Type then
                        (if UI_Lt (Modulus_Val, UI_Expon (2, 8)) then
                              New_Modular_Constant (Value => Modulus_Val,
                                                    Typ => EW_BitVector_8_Type)
                         else
                                Why_Empty)
                      elsif Typ = EW_BitVector_16_Type then
                        (if UI_Lt (Modulus_Val, UI_Expon (2, 16)) then
                              New_Modular_Constant
                           (Value => Modulus_Val,
                            Typ => EW_BitVector_16_Type)
                         else
                                Why_Empty)
                      elsif Typ = EW_BitVector_32_Type then
                        (if UI_Lt (Modulus_Val, UI_Expon (2, 32)) then
                              New_Modular_Constant
                           (Value => Modulus_Val,
                            Typ => EW_BitVector_32_Type)
                         else
                                Why_Empty)
                      elsif Typ = EW_BitVector_64_Type then
                        (if UI_Lt (Modulus_Val, UI_Expon (2, 64)) then
                              New_Modular_Constant
                           (Value => Modulus_Val,
                            Typ => EW_BitVector_64_Type)
                         else
                            Why_Empty)
                      else
                         raise Program_Error);

            Emit (Section,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Local (E_Symb (E, WNE_Attr_Modulus)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Base_Type,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Location    => No_Location,
                     Def         => +Modul));
         end;

      --  Compute and declare the small attribute of fixed point types

      elsif Has_Fixed_Point_Type (E) then
         declare
            Small     : constant Ureal := Small_Value (E);
            Num_Small : constant W_Term_OId :=
              New_Integer_Constant (Value => Norm_Num (Small));
            Den_Small : constant W_Term_OId :=
              New_Integer_Constant (Value => Norm_Den (Small));
         begin
            Emit (Section,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Local (E_Symb (E, WNE_Small_Num)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Base_Type,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Location    => No_Location,
                     Def         => +Num_Small));
            Emit (Section,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Local (E_Symb (E, WNE_Small_Den)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Base_Type,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Location    => No_Location,
                     Def         => +Den_Small));
         end;
      end if;

      --  Compute and declare the first and last attributes of E
      --  If they are static, those are constants.
      --  Otherwise, we declare logic functions for them, with arguments for
      --  the variables they may read. These functions will be defined later
      --  in the axiom module of E.
      --  Compute the binders as the objects are not declared at that point.
      --  First and Last attributes of Itypes are never used, do not declare
      --  them.

      if not (Type_Is_Modeled_As_Base (E) and then Is_Itype (E)) then
         Emit (Section,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_First)),
                  Items       => Get_Binders_From_Expression
                    (Low_Bound (Rng), Compute => True),
                  Return_Type => Base_Type,
                  Location    => No_Location,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +First));
         Emit (Section,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_Last)),
                  Items       => Get_Binders_From_Expression
                    (High_Bound (Rng), Compute => True),
                  Return_Type => Base_Type,
                  Location    => No_Location,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +Last));
      end if;
   end Define_Scalar_Attributes;

   ----------------------------
   -- Define_Scalar_Rep_Proj --
   ----------------------------

   procedure Define_Scalar_Rep_Proj
     (File : W_Section_Id;
      E      : Entity_Id)
   is
      Rep_Type : constant W_Type_Id := Base_Why_Type (E);

      function Pick_Clone return W_Module_Id;
      --  Pick the correct theory to clone depending on the scalar type.

      function Pick_Clone return W_Module_Id is
      begin
         if Rep_Type = EW_Float_32_Type then
            return Rep_Proj_Float32;
         elsif Rep_Type = EW_Float_64_Type then
            return Rep_Proj_Float64;
         elsif Rep_Type = EW_Int_Type then
            return Rep_Proj_Int;
         elsif Why_Type_Is_BitVector (Rep_Type) then
            declare
               Modulus_Val : constant Uint := Modulus (E);
            begin
               return (if Rep_Type = EW_BitVector_8_Type then
                         (if UI_Lt (Modulus_Val, UI_Expon (2, 8)) then
                             Rep_Proj_Lt8
                          else
                             Rep_Proj_8)
                       elsif Rep_Type = EW_BitVector_16_Type then
                         (if UI_Lt (Modulus_Val, UI_Expon (2, 16)) then
                             Rep_Proj_Lt16
                          else
                             Rep_Proj_16)
                       elsif Rep_Type = EW_BitVector_32_Type then
                         (if UI_Lt (Modulus_Val, UI_Expon (2, 32)) then
                             Rep_Proj_Lt32
                          else
                             Rep_Proj_32)
                       elsif Rep_Type = EW_BitVector_64_Type then
                         (if UI_Lt (Modulus_Val, UI_Expon (2, 64)) then
                             Rep_Proj_Lt64
                          else
                             Rep_Proj_64)
                       else
                          raise Program_Error);
            end;
         else
            raise Program_Error;
         end if;
      end Pick_Clone;

      Default_Clone_Subst : constant W_Clone_Substitution_Array :=
        (1 => New_Clone_Substitution
           (Kind      => EW_Type_Subst,
            Orig_Name => New_Name (Symbol => NID ("t")),
            Image     => To_Why_Type (E)));

      In_Range_Substs : constant W_Clone_Substitution_Array :=
        (if Is_Modular_Integer_Type (E) then
             (1 => New_Clone_Substitution
              (Kind => EW_Predicate,
               Orig_Name => New_Name (Symbol => NID ("in_range")),
               Image => Get_Name (E_Symb (E, WNE_Range_Pred))),
              2 => New_Clone_Substitution
                (Kind => EW_Predicate,
                 Orig_Name => New_Name (Symbol => NID ("in_range_int")),
                 Image => Get_Name (E_Symb (E, WNE_Range_Pred_BV_Int))))
         else
           (1 => New_Clone_Substitution
                (Kind => EW_Predicate,
                 Orig_Name => New_Name (Symbol => NID ("in_range")),
                 Image => Get_Name (E_Symb (E, WNE_Range_Pred)))));

      Mod_Clone_Subst : constant W_Clone_Substitution_Array :=
        (if Has_Modular_Integer_Type (E)
         and then Modulus (E) /= UI_Expon (2, Modular_Size (E))
         then
           (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => To_Local (E_Symb (E, WNE_Attr_Modulus)),
                 Image     => Get_Name (E_Symb (E, WNE_Attr_Modulus))))
         else (1 .. 0 => <>));

      Range_Type_Subst : constant W_Clone_Substitution_Array :=
        (if Is_Range_Type_In_Why (E) then
           (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID ("to_rep")),
                 Image     => To_Local (E_Symb (E, WNE_To_Rep))))
         else (1 .. 0 => <>));

      Substs : constant W_Clone_Substitution_Array :=
        Default_Clone_Subst & In_Range_Substs & Mod_Clone_Subst
        & Range_Type_Subst;

      Clone : constant W_Module_Id := Pick_Clone;
   begin

      Add_With_Clause (File, E_Module (E), EW_Clone_Default);

      if Is_Modular_Integer_Type (E) then

         Add_With_Clause (File, MF_BVs (Rep_Type).Module, EW_Clone_Default);
      elsif Is_Floating_Point_Type (E) then
         Add_With_Clause (File,
                          MF_Floats (Rep_Type).Module,
                          EW_Clone_Default);
      end if;

      if Is_Range_Type_In_Why (E) then

         --  For range types, declare a renaming of t'int which will be used
         --  to clone the representative theory.

         declare
            Var     : constant W_Identifier_Id :=
              New_Identifier
                (Name => "x", Typ => EW_Abstract (E));
            Binders : constant Binder_Array :=
              Binder_Array'(1 => Binder_Type'(B_Name => Var,
                                              others => <>));
         begin

            Emit (File,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (E_Symb (E, WNE_To_Rep)),
                     Binders     => Binders,
                     Return_Type => EW_Int_Type,
                     Def         =>
                       New_Call
                         (Domain => EW_Term,
                          Name   => E_Symb (E, WNE_Int_Proj),
                          Args   => (1 => +Var),
                          Typ    => EW_Int_Type),
                     Location    => No_Location,
                     Labels      => Name_Id_Sets.Empty_Set));
         end;
      end if;

      Emit (File,
            New_Clone_Declaration (Theory_Kind   => EW_Module,
                                   Clone_Kind    => EW_Export,
                                   As_Name       => No_Name,
                                   Origin        => Clone,
                                   Substitutions => Substs));

      --  Declare metas for functions projecting values of why abstract types
      --  to concrete values
      --    - the defined type is why abstract type. To see the concrete value
      --      in a counterexample, it is needed to project the value of this
      --      type using projection function
      --    - the function F is projection function for abstract type T if it
      --      is marked with the meta "model_projection" and has a single
      --      argument of type T.
      --    - the projection functions are cloned from projection functions
      --      defined in ada__model.mlw
      --    - Since for why3, the cloned function and the original function are
      --      two different functions, it is necessary to emit projection meta
      --      for cloned projection functions.

      --  Note that if E is dynamic type, to_rep is not projection function
      Emit_Projection_Metas (Section => File, Projection_Fun => "to_rep");

   end Define_Scalar_Rep_Proj;

   -------------------------------------
   -- Get_Fixed_Point_Mult_Div_Theory --
   -------------------------------------

   function Get_Fixed_Point_Mult_Div_Theory
     (Typ_Left, Typ_Right, Typ_Result : Entity_Id)
      return M_Fixed_Point_Mult_Div_Type
   is
      Module_Name : constant Name_Id :=
        Get_Fixed_Point_Mult_Div_Theory_Name (Typ_Left   => Typ_Left,
                                              Typ_Right  => Typ_Right,
                                              Typ_Result => Typ_Result);
   begin
      return M_Fixed_Point_Mult_Div (Module_Name);
   end Get_Fixed_Point_Mult_Div_Theory;

   ------------------------------------------
   -- Get_Fixed_Point_Mult_Div_Theory_Name --
   ------------------------------------------

   function Get_Fixed_Point_Mult_Div_Theory_Name
     (Typ_Left, Typ_Right, Typ_Result : Entity_Id) return Name_Id
   is
      L_Small   : constant Ureal := Small_Value (Typ_Left);
      R_Small   : constant Ureal :=
        (if Has_Fixed_Point_Type (Typ_Right) then
           Small_Value (Typ_Right)
         elsif Has_Signed_Integer_Type (Typ_Right) then
           Ureal_1
         else raise Program_Error);
      Res_Small : constant Ureal := Small_Value (Typ_Result);

      Name      : constant String :=
        To_String (WNE_Fixed_Point_Mult_Div_Prefix) & "__"
        & Ureal_Name (L_Small) & "__"
        & Ureal_Name (R_Small) & "__"
        & Ureal_Name (Res_Small);
   begin
      return NID (Name);
   end Get_Fixed_Point_Mult_Div_Theory_Name;

   ----------------------------
   -- Get_Fixed_Point_Theory --
   ----------------------------

   function Get_Fixed_Point_Theory (Typ : Entity_Id) return M_Fixed_Point_Type
   is
      Module_Name : constant Name_Id :=
        Get_Fixed_Point_Theory_Name (Typ => Typ);
   begin
      return M_Fixed_Points (Module_Name);
   end Get_Fixed_Point_Theory;

   ---------------------------------
   -- Get_Fixed_Point_Theory_Name --
   ---------------------------------

   function Get_Fixed_Point_Theory_Name (Typ : Entity_Id) return Name_Id
   is
      Small : constant Ureal := Small_Value (Typ);
      Name  : constant String :=
        To_String (WNE_Fixed_Point_Prefix) & "__"
        & Ureal_Name (Small);
   begin
      return NID (Name);
   end Get_Fixed_Point_Theory_Name;

   ------------------
   -- Num_Constant --
   ------------------

   function Num_Constant (Ty : Entity_Id; N : Node_Id) return W_Term_Id is
   begin
      if Is_Modular_Integer_Type (Ty) then
         return New_Modular_Constant
           (Value => Expr_Value (N),
            Typ => Base_Why_Type (Ty));
      elsif Is_Discrete_Type (Ty) then
         return New_Integer_Constant (Value => Expr_Value (N));
      elsif Is_Fixed_Point_Type (Ty) then
         return New_Fixed_Constant
           (Value => Expr_Value (N), Typ => Base_Why_Type (Ty));
      elsif Is_Floating_Point_Type (Ty) then
         if Is_Fixed_Point_Type (Etype (N))
           and then From_Real_Range_Specification (N)
         then
            --  Allow Real ranges to use fixed point values; see acats c35704a
            return +Insert_Simple_Conversion
              (Ada_Node       => N,
               Domain         => EW_Term,
               Expr           =>
                 New_Fixed_Constant
                 (Value => Expr_Value (N),
                  Typ   => Base_Why_Type (Etype (N))),
               To             => Base_Why_Type (Ty));
         else
            return New_Float_Constant (Value => Expr_Value_R (N),
                                       Typ   => Base_Why_Type (Ty));
         end if;
      else
         return New_Real_Constant (Value => Expr_Value_R (N));
      end if;
   end Num_Constant;

end Why.Gen.Scalars;
