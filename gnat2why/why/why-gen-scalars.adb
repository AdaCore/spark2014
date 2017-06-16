------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Atree;               use Atree;
with Common_Containers;   use Common_Containers;
with Namet;               use Namet;
with Sem_Eval;            use Sem_Eval;
with Sinfo;               use Sinfo;
with SPARK_Util;          use SPARK_Util;
with SPARK_Util.Types;    use SPARK_Util.Types;
with Stand;               use Stand;
with Uintp;               use Uintp;
with Urealp;              use Urealp;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
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

   procedure Define_Scalar_Attributes
     (Section    : W_Section_Id;
      E          : Entity_Id;
      Base_Type  : W_Type_Id);
   --  Define the attributes first, last, modulus, small for the given type.

   function Num_Constant (Ty : Entity_Id; N : Node_Id) return W_Term_Id;
   --  N must be a static expression. This function evaluates N as an Uint (if
   --  Ty is a discrete type or a fixed-point type) or as real (if Ty is not
   --  discrete)

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
              and then Modulus (E) /= UI_Expon (2, Esize (E))
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
         Fixed_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Fixed_Point_Type (E) then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Local (E_Symb (E, WNE_Attr_Small)),
                  Image     => To_Local (E_Symb (E, WNE_Attr_Small))))
            else (1 .. 0 => <>));
      begin

         return
           Default_Clone_Subst &
           Rep_Type_Clone_Substitution &
           Static_Clone_Subst &
           Dynamic_Conv_Subst &
           Mod_Clone_Subst &
           Range_Int_Clone_Subst &
           Fixed_Clone_Subst;
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
           and then ((Ty = EW_BitVector_8_Type
                      and then Modulus (E) = UI_Expon (Uint_2, Uint_8))
                     or else
                       (Ty = EW_BitVector_16_Type
                        and then Modulus (E) = UI_Expon (Uint_2, Uint_16))
                     or else
                       (Ty = EW_BitVector_32_Type
                        and then Modulus (E) = UI_Expon (Uint_2, Uint_32))
                     or else
                       (Ty = EW_BitVector_64_Type
                        and then Modulus (E) = UI_Expon (Uint_2, Uint_64)))
           and then Intval (Low_Bound (Scalar_Range (E))) = Uint_0
           and then Intval (High_Bound (Scalar_Range (E)))
                  = UI_Sub (Modulus (E), Uint_1)
         then

            --  In which case we know that all values are necessary in range,
            --  So we define the range predicate as always true.
            Emit (File,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain  => EW_Pred,
                     Name    => To_Local (E_Symb (E, Name)),
                     Def     => +True_Pred,
                     Labels  => Name_Id_Sets.Empty_Set,
                     Binders => (1 => Binder_Type'(B_Name => Var,
                                                   others => <>))));

            --  And we directly use the function uint_in_range from the
            --  underlying why3 theory for checking the range againts integers
            --  instead of generating it.
            Emit (File,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain  => EW_Pred,
                     Name    => To_Local (E_Symb (E, WNE_Range_Pred_BV_Int)),
                     Def     => +New_Identifier (Name => "uint_in_range x",
                                                 Module =>
                                                   MF_BVs
                                                     (Base_Why_Type (E))
                                                 .Module),
                     Labels  => Name_Id_Sets.Empty_Set,
                     Binders => (1 => Binder_Type'
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
              and then UR_Eq (Realval (Low_Bound (Scalar_Range (E))),
                              Realval (Low_Bound (Scalar_Range
                                (if Ty = EW_Float_32_Type
                                     then Standard_Float
                                     else Standard_Long_Float))))
              and then UR_Eq (Realval (High_Bound (Scalar_Range (E))),
                              Realval (High_Bound (Scalar_Range
                                (if Ty = EW_Float_32_Type
                                     then Standard_Float
                                     else Standard_Long_Float))))
            then

               --  In which case we know that all values are necessary in range
               --  so we define the range predicate as "is_finite".
               Emit (File,
                     Why.Gen.Binders.New_Function_Decl
                       (Domain  => EW_Pred,
                        Name    => To_Local (E_Symb (E, Name)),
                        Def     => New_Call (Domain => EW_Pred,
                                             Name   =>
                                               MF_Floats (Ty).Is_Finite,
                                             Args   => (1 => +Var)),
                        Labels  => Name_Id_Sets.Empty_Set,
                        Binders => (1 => Binder_Type'(B_Name => Var,
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
                    (Domain  => EW_Pred,
                     Name    => To_Local (E_Symb (E, Name)),
                     Def     => +Def,
                     Labels  => Name_Id_Sets.Empty_Set,
                     Binders => Binders));

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

      --  declare the abstract type
      --  if the type is dynamic, declare an alias of its base type

      if not Is_Static then
         Emit (File,
               New_Type_Decl
                 (Name  => Why_Name,
                  Alias => Base_Type_In_Why));
      else
         Emit (File,
               New_Type_Decl
                 (Name => Why_Name,
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
      Base_Type  : W_Type_Id) is

      Rng : constant Node_Id := Get_Range (E);

      First : constant W_Term_OId :=
        (if Is_Static_Expression (Low_Bound (Rng))
         then +Num_Constant (E, Low_Bound (Rng))
         else Why_Empty);

      Last : constant W_Term_OId :=
        (if Is_Static_Expression (High_Bound (Rng))
         then +Num_Constant (E, High_Bound (Rng))
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
                     Def         => +Modul));
         end;

      --  Compute and declare the small attribute of fixed point types

      elsif Has_Fixed_Point_Type (E) then
         declare
            Inv_Small : constant Ureal := UR_Div (Uint_1, Small_Value (E));
            Small     : W_Term_OId;
         begin
            pragma Assert (Norm_Den (Inv_Small) = Uint_1);
            Small := New_Integer_Constant (Value => Norm_Num (Inv_Small));

            Emit (Section,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Local (E_Symb (E, WNE_Attr_Small)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Base_Type,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Def         => +Small));
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
         and then Modulus (E) /= UI_Expon (2, Esize (E))
         then
           (1 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => To_Local (E_Symb (E, WNE_Attr_Modulus)),
                 Image     => Get_Name (E_Symb (E, WNE_Attr_Modulus))))
         else (1 .. 0 => <>));

      Substs : constant W_Clone_Substitution_Array :=
        Default_Clone_Subst & In_Range_Substs & Mod_Clone_Subst;

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

      Emit (File,
            New_Clone_Declaration (Theory_Kind   => EW_Module,
                                   Clone_Kind    => EW_Export,
                                   As_Name       => No_Name,
                                   Origin        => Clone,
                                   Substitutions => Substs));

      Emit_Projection_Metas (Section => File,
                             Projection_Fun => "to_rep");

      --  declare metas for functions projecting values of why abstract types
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

      if Is_Discrete_Type (E) then
         --  Note that if E is dynamic type, to_rep is not projection function
         Emit_Projection_Metas (Section => File, Projection_Fun => "to_rep");
      end if;

   end Define_Scalar_Rep_Proj;

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
         return New_Fixed_Constant (Value => Expr_Value (N));
      elsif Is_Floating_Point_Type (Ty) then
         if Is_Fixed_Point_Type (Etype (N)) and then
           Nkind (Parent (N)) = N_Real_Range_Specification
         then
            --  Allow Real ranges to use fixed point values; see acats c35704a
            return +Insert_Simple_Conversion
              (Ada_Node       => N,
               Domain         => EW_Term,
               Expr           => New_Fixed_Constant (Value => Expr_Value (N)),
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
