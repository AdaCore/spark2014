------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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
with Namet;               use Namet;
with Nlists;              use Nlists;
with Sem_Eval;            use Sem_Eval;
with Sinfo;               use Sinfo;
with Uintp;               use Uintp;
with Urealp;              use Urealp;

with SPARK_Util;          use SPARK_Util;

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

with Gnat2Why.Util;       use Gnat2Why.Util;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      E          : Entity_Id;
      Base_Type  : W_Type_Id;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId;
      Small      : W_Term_OId;
      Is_Static  : Boolean);
   --  Define the attributes first, last, modulus, small for the given type.

   function Num_Constant (Ty : Entity_Id; N : Node_Id) return W_Term_Id;
   --  N must be a static expression. This function evaluates N as an Uint (if
   --  Ty is a discrete type or a fixed-point type) or as real (if Ty is not
   --  discrete)

   -------------------------
   -- Declare_Scalar_Type --
   -------------------------

   procedure Declare_Scalar_Type
     (Theory : W_Theory_Declaration_Id;
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
         Has_Round_Real : constant Boolean :=
           Is_Single_Precision_Floating_Point_Type (E)
             or else
           Is_Double_Precision_Floating_Point_Type (E);
         Round_Id : constant W_Identifier_Id :=
           (if Is_Single_Precision_Floating_Point_Type (E) then
                 M_Floating.Round_Single
            elsif Is_Double_Precision_Floating_Point_Type (E) then
                 M_Floating.Round_Double
            else
               M_Floating.Round);
         Default_Clone_Subst : constant W_Clone_Substitution_Id :=
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Name (Symbol => NID ("t")),
              Image     => Why_Name);
         Rep_Type_Clone_Substitution : constant W_Clone_Substitution_Array :=
           (if not Is_Static and Has_Discrete_Type (E) then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Type_Subst,
                  Orig_Name => New_Name
                    (Symbol => NID ("rep_type")),
                  Image     => Get_Name (Base_Why_Type (E))))
            else (1 .. 0 => <>));
         Round_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Has_Round_Real then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Local (E_Symb (E, WNE_Float_Round_Tmp)),
                    Image     => To_Name (Round_Id)))
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
                   To_Name
                     (Conversion_Name
                        (From => Base_Type_In_Why,
                         To   => Base_Why_Type (E)))),
               2 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID ("base_of_rep")),
                 Image     =>
                   To_Name
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
              and then Modulus (E) /= UI_Expon (2, 8)
              and then Modulus (E) /= UI_Expon (2, 16)
              and then Modulus (E) /= UI_Expon (2, 32)
              and then Modulus (E) /= UI_Expon (2, 64)
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

         --  If the type Entity has a rounding operation, use it in the clone
         --  substitution to replace the default one.

         return
           Default_Clone_Subst &
           Rep_Type_Clone_Substitution &
           Round_Clone_Subst &
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
              (Has_Modular_Integer_Type (E) and Ty = EW_Int_Type)
            then
               New_Identifier
              (Symbol => NID ("first_int"),
               Domain => EW_Term,
               Typ    => Ty)
            else To_Local (E_Symb (E, WNE_Attr_First)));
         Lst : constant W_Identifier_Id :=
           (if not Is_Static or else
              (Has_Modular_Integer_Type (E) and Ty = EW_Int_Type)
            then
               New_Identifier
              (Symbol => NID ("last_int"),
               Domain => EW_Term,
               Typ    => Ty)
            else To_Local (E_Symb (E, WNE_Attr_Last)));
      begin
         if Has_Static_Discrete_Predicate (E) then
            declare
               Pred   : Node_Id := First (Static_Discrete_Predicate (E));
            begin
               Def := False_Pred;

               --  The compiler has already prepared the static predicate
               --  in such a way that it is simply a list of ranges which
               --  represent the type

               while Present (Pred) loop
                  declare
                     Rng   : constant Node_Id := Get_Range (Pred);
                     First : constant W_Term_Id :=
                       (if Why_Type_Is_BitVector (Ty) then
                             +Insert_Simple_Conversion
                          (Domain => EW_Term,
                           Expr   => +Num_Constant (E, Low_Bound (Rng)),
                           To     => Ty)
                        else
                           Num_Constant (E, Low_Bound (Rng)));
                     Last  : constant W_Term_Id :=
                       (if Why_Type_Is_BitVector (Ty) then
                             +Insert_Simple_Conversion
                          (Domain => EW_Term,
                           Expr   => +Num_Constant (E, High_Bound (Rng)),
                           To     => Ty)
                        else
                           Num_Constant (E, High_Bound (Rng)));
                  begin
                     Def :=
                       +New_Or_Else_Expr
                       (Domain => EW_Pred,
                        Left   => +Def,
                        Right  =>
                          New_Range_Expr (Domain => EW_Pred,
                                          Low    => +First,
                                          High   => +Last,
                                          Expr   => +Var));
                     Next (Pred);
                  end;
               end loop;
            end;
         end if;

         --  For a static type with static predicates, the range constraints
         --  are already included in the predicate's constraints.
         --  Otherwise, add the range constraints to the predicate.

         if not Is_Static
           or else not Has_Static_Discrete_Predicate (E)
         then
            Def :=
              +New_And_Expr
              (Domain => EW_Pred,
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
            Emit (Theory,
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
      begin
         if Is_Static then
            if Has_Modular_Integer_Type (E) then
               declare
                  Modulus_Val : constant Uint := Modulus (E);
                  Typ : constant W_Type_Id := Base_Why_Type (E);
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
               return Static_Floating_Point;
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
               return Dynamic_Floating_Point;
            end if;
         end if;
      end Pick_Clone;

      --  Local variables

      First, Last, Modul, Small : W_Term_OId := Why_Empty;
      Rng                       : constant Node_Id := Get_Range (E);

   --  Start of Declare_Scalar_Type

   begin

      --  declare the abstract type
      --  if the type is dynamic, declare an alias of its base type

      if not Is_Static then
         Emit (Theory,
               New_Type_Decl
                 (Name  => Why_Name,
                  Alias => Base_Type_In_Why));
      else
         Emit (Theory,
               New_Type_Decl
                 (Name => Why_Name,
                  Labels => Name_Id_Sets.Empty_Set));
      end if;

      --  retrieve and declare the attributes first, last and modulus

      if Has_Modular_Integer_Type (E) then
         declare
            Modulus_Val : constant Uint := Modulus (E);
            Typ : constant W_Type_Id := Base_Why_Type (E);
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
         end;
      end if;

      if Has_Fixed_Point_Type (E) then
         declare
            Inv_Small : constant Ureal := UR_Div (Uint_1, Small_Value (E));
         begin
            pragma Assert (Norm_Den (Inv_Small) = Uint_1);
            Small := New_Integer_Constant (Value => Norm_Num (Inv_Small));
         end;
      end if;

      if Is_Static_Expression (Low_Bound (Rng)) then
         First := +Num_Constant (E, Low_Bound (Rng));
      end if;
      if Is_Static_Expression (High_Bound (Rng)) then
         Last := +Num_Constant (E, High_Bound (Rng));
      end if;

      Define_Scalar_Attributes
        (Theory    => Theory,
         E         => E,
         Base_Type => Base_Why_Type (E),
         First     => First,
         Last      => Last,
         Modulus   => Modul,
         Small     => Small,
         Is_Static => Is_Static);

      --  define first_int and last_int for static modular types

      if Is_Static and then Is_Modular_Integer_Type (E) then
         Emit (Theory,
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
         Emit (Theory,
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

      Emit (Theory,
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
     (Theory     : W_Theory_Declaration_Id;
      E          : Entity_Id;
      Base_Type  : W_Type_Id;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId;
      Small      : W_Term_OId;
      Is_Static  : Boolean) is
   begin
      if Is_Static then
         Emit (Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_First)),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => Base_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +First));
         Emit (Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_Last)),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => Base_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +Last));
      end if;
      if Modulus /= Why_Empty then
         Emit (Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_Modulus)),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => Base_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +Modulus));
      end if;
      if Small /= Why_Empty then
         Emit (Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (E, WNE_Attr_Small)),
                  Binders     => (1 .. 0 => <>),
                  Return_Type => Base_Type,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Def         => +Small));
      end if;
   end Define_Scalar_Attributes;

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
      else
         return New_Real_Constant (Value => Expr_Value_R (N));
      end if;
   end Num_Constant;

end Why.Gen.Scalars;
