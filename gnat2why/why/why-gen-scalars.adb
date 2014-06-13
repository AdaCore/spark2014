------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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
with Nlists;              use Nlists;
with Sem_Eval;            use Sem_Eval;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Snames;              use Snames;
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

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;
with Gnat2Why.Util;       use Gnat2Why.Util;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId;
      Small      : W_Term_OId);
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
      Why_Name  : constant W_Name_Id := To_Why_Type (E, Local => True);
      Is_Static : constant Boolean := not Type_Is_Modeled_As_Int_Or_Real (E);

      function Pick_Clone return W_Module_Id;
      --  Choose the correct module to clone

      function Compute_Clone_Subst return W_Clone_Substitution_Array;
      --  generate the substitutions to be passed to the clone

      procedure Generate_Range_Predicate;
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
                 Floating_Round_Single
            elsif Is_Double_Precision_Floating_Point_Type (E) then
                 Floating_Round_Double
            else
               Floating_Round);
         Default_Clone_Subst : constant W_Clone_Substitution_Id :=
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Identifier (Name => "t"),
              Image     => New_Identifier (Why_Name));
         Round_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Has_Round_Real then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Ident (WNE_Float_Round_Tmp),
                    Image     => Round_Id))
            else (1 .. 0 => <>));
         Static_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Static then
              (1 => New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => To_Ident (WNE_Attr_First),
                    Image     => To_Ident (WNE_Attr_First)),
               2 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Ident (WNE_Attr_Last),
                  Image     => To_Ident (WNE_Attr_Last)))
            else (1 .. 0 => <>));
         Mod_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Modular_Integer_Type (E) then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Ident (WNE_Attr_Modulus),
                  Image     => To_Ident (WNE_Attr_Modulus)))
            else (1 .. 0 => <>));
         Range_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Static or else Is_Discrete_Type (E) then
              (1 => New_Clone_Substitution
               (Kind      => EW_Predicate,
                Orig_Name => To_Ident (WNE_Range_Pred),
                Image     => To_Ident (WNE_Range_Pred)))
            else (1 .. 0 => <>));
         Fixed_Clone_Subst : constant W_Clone_Substitution_Array :=
           (if Is_Fixed_Point_Type (E) then
                (1 => New_Clone_Substitution
                 (Kind      => EW_Function,
                  Orig_Name => To_Ident (WNE_Attr_Small),
                  Image     => To_Ident (WNE_Attr_Small)))
            else (1 .. 0 => <>));
      begin

         --  If the type Entity has a rounding operation, use it in the clone
         --  substitution to replace the default one.

         return
           Default_Clone_Subst &
           Round_Clone_Subst &
           Static_Clone_Subst &
           Mod_Clone_Subst &
           Range_Clone_Subst &
           Fixed_Clone_Subst;
      end Compute_Clone_Subst;

      ------------------------------
      -- Generate_Range_Predicate --
      ------------------------------

      procedure Generate_Range_Predicate is
         Ty  : constant W_Type_Id := Base_Why_Type (E);
         Var : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => Ty);
         Def : W_Pred_Id := Why_Empty;
      begin
         if Is_Static then
            if Has_Predicates (E) then
               declare
                  Pred   : Node_Id := First (Static_Discrete_Predicate (E));
               begin
                  Def := False_Pred;
                  while Present (Pred) loop
                     declare
                        Rng   : constant Node_Id := Get_Range (Pred);
                        First : constant W_Term_Id :=
                          Num_Constant (E, Low_Bound (Rng));
                        Last  : constant W_Term_Id :=
                          Num_Constant (E, High_Bound (Rng));
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

            else
               declare
                  First : constant W_Identifier_Id :=
                    New_Identifier
                      (Symbol => Get_Symbol (To_Ident (WNE_Attr_First)),
                       Domain => EW_Term,
                       Typ    => Ty);
                  Last : constant W_Identifier_Id :=
                    New_Identifier
                      (Symbol => Get_Symbol (To_Ident (WNE_Attr_Last)),
                       Domain => EW_Term,
                       Typ    => Ty);
               begin
                  Def :=
                    +New_Range_Expr (Domain => EW_Pred,
                                     Low    => +First,
                                     High   => +Last,
                                     Expr   => +Var);
               end;
            end if;
         end if;

         Emit (Theory,
               Why.Gen.Binders.New_Function_Decl
                 (Domain  => EW_Pred,
                  Name    => To_Ident (WNE_Range_Pred),
                  Def     => +Def,
                  Labels  => Name_Id_Sets.Empty_Set,
                  Binders =>
                    (1 => Binder_Type'(B_Name => Var,
                                       others => <>))));
      end Generate_Range_Predicate;

      ----------------
      -- Pick_Clone --
      ----------------

      function Pick_Clone return W_Module_Id is
      begin
         if Is_Static then
            if Is_Modular_Integer_Type (E) then
               return Static_Modular;
            elsif Is_Discrete_Type (E) then
               return Static_Discrete;
            elsif Is_Fixed_Point_Type (E) then
               return Static_Fixed_Point;
            else
               pragma Assert (Is_Floating_Point_Type (E));
               return Static_Floating_Point;
            end if;
         else
            if Is_Modular_Integer_Type (E) then
               return Dynamic_Modular;
            elsif Is_Discrete_Type (E) then
               return Dynamic_Discrete;
            elsif Is_Fixed_Point_Type (E) then
               return Dynamic_Fixed_Point;
            else
               pragma Assert (Is_Floating_Point_Type (E));
               return Dynamic_Floating_Point;
            end if;
         end if;
      end Pick_Clone;

      --  Local variables

      First, Last, Modul, Small : W_Term_OId := Why_Empty;
      Rng                       : constant Node_Id := Get_Range (E);

   --  Start of Declare_Scalar_Type

   begin

      if not Is_Static_Subtype (E) and then Is_Discrete_Type (E) then
         declare
            Why_Base_Type : constant W_Type_Id := EW_Abstract (Base_Type (E));

            Default_Clone_Subst : constant W_Clone_Substitution_Id :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Identifier (Name => "base"),
                 Image     => New_Identifier (Why_Name));

            To_Int_Clone_Subst : constant W_Clone_Substitution_Id :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Identifier (Name => "to_int_base"),
                 Image     => Conversion_Name
                                (From => Why_Base_Type,
                                 To   => EW_Int_Type));

            Of_Int_Clone_Subst : constant W_Clone_Substitution_Id :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Identifier (Name => "of_int_base"),
                 Image     => Conversion_Name
                                (To   => Why_Base_Type,
                                 From => EW_Int_Type));
         begin

            --  declare the abstract type

            Emit (Theory,
                  New_Type_Decl
                    (Name       => Why_Name,
                     Labels     => Name_Id_Sets.Empty_Set,
                     Definition => New_Transparent_Type_Definition
                       (Domain          => EW_Term,
                        Type_Definition => Why_Base_Type)));

            --  clone the appropriate module

            Emit (Theory,
                  New_Clone_Declaration
                    (Theory_Kind   => EW_Module,
                     Clone_Kind    => EW_Export,
                     Origin        =>
                       (if Depends_On_Discriminant (Rng) then
                             Dynamic_Discrete_Base
                        else Dynamic_Discrete),
                     Substitutions =>
                       Default_Clone_Subst & To_Int_Clone_Subst &
                       Of_Int_Clone_Subst));

            return;
         end;
      end if;

      --  declare the abstract type

      Emit (Theory,
            New_Type_Decl
              (Name => Why_Name,
               Labels => Name_Id_Sets.To_Set (NID ("""bounded_type"""))));

      --  retrieve and declare the attributes first, last and modulus

      if Is_Modular_Integer_Type (E) then
         Modul := New_Integer_Constant (Value => Modulus (E));
      end if;

      if Is_Fixed_Point_Type (E) then
         declare
            Inv_Small : constant Ureal := UR_Div (Uint_1, Small_Value (E));
         begin
            pragma Assert (Norm_Den (Inv_Small) = Uint_1);
            Small := New_Integer_Constant (Value => Norm_Num (Inv_Small));
         end;
      end if;

      if Is_Static_Expression (Low_Bound (Rng)) then
         First := Num_Constant (E, Low_Bound (Rng));
      end if;
      if Is_Static_Expression (High_Bound (Rng)) then
         Last := Num_Constant (E, High_Bound (Rng));
      end if;

      Define_Scalar_Attributes
        (Theory    => Theory,
         Base_Type => Get_Base_Type (Base_Why_Type (E)),
         First     => First,
         Last      => Last,
         Modulus   => Modul,
         Small     => Small);

      Generate_Range_Predicate;

      --  clone the appropriate module

      Emit (Theory,
            New_Clone_Declaration (Theory_Kind   => EW_Module,
                                   Clone_Kind    => EW_Export,
                                   Origin        => Pick_Clone,
                                   Substitutions => Compute_Clone_Subst));
   end Declare_Scalar_Type;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId;
      Small      : W_Term_OId)
   is
      type Scalar_Attr is (S_First, S_Last, S_Modulus, S_Small);

      type Attr_Info is record
         Attr_Id : Attribute_Id;
         Value   : W_Term_Id;
      end record;

      Attr_Values : constant array (Scalar_Attr) of Attr_Info :=
                      (S_First   => (Attribute_First, First),
                       S_Last    => (Attribute_Last, Last),
                       S_Modulus => (Attribute_Modulus, Modulus),
                       S_Small   => (Attribute_Small, Small));
   begin
      for J in Attr_Values'Range loop

         --  We force generation of first/last, but potentially skip
         --  Modulus/Small

         if J in S_First | S_Last or else
           Attr_Values (J).Value /= Why_Empty
         then
            Emit (Theory,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       To_Ident (Attr_To_Why_Name (Attr_Values (J).Attr_Id)),
                     Binders     => (1 .. 0 => <>),
                     Return_Type => Why_Types (Base_Type),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Def         => W_Expr_Id (Attr_Values (J).Value)));
         end if;
      end loop;
   end Define_Scalar_Attributes;

   ------------------
   -- Num_Constant --
   ------------------

   function Num_Constant (Ty : Entity_Id; N : Node_Id) return W_Term_Id is
   begin
      if Is_Discrete_Type (Ty) then
         return New_Integer_Constant (Value => Expr_Value (N));
      elsif Is_Fixed_Point_Type (Ty) then
         return New_Fixed_Constant (Value => Expr_Value (N));
      else
         return New_Real_Constant (Value => Expr_Value_R (N));
      end if;
   end Num_Constant;

end Why.Gen.Scalars;
