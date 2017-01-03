------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Atree;                 use Atree;
with Common_Containers;     use Common_Containers;
with GNAT.Source_Info;
with Gnat2Why.Types;        use Gnat2Why.Types;
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with Sem_Eval;              use Sem_Eval;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with SPARK_Util;            use SPARK_Util;
with SPARK_Util.Types;      use SPARK_Util.Types;
with Stand;                 use Stand;
with String_Utils;          use String_Utils;
with Uintp;                 use Uintp;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Inter;             use Why.Inter;

package body Why.Gen.Arrays is

   procedure Declare_Constrained
     (Section : W_Section_Id;
      Und_Ent : Entity_Id);
   --  Output a declaration for statically constrained array types.
   --  @param Section The section in which the declaration should be added
   --  @param Und_Ent The entity of the array type to be translated. It should
   --                 be a statically constrained array type.
   --  Here we don't need a name for the type in why as no type will be
   --  declared in this module.

   procedure Declare_Unconstrained
     (Section        : W_Section_Id;
      Why3_Type_Name : W_Name_Id;
      Und_Ent        : Entity_Id);
   --  Output a declaration for unconstrained and dynamically constrained array
   --  types.
   --  @param Section The section in which the declaration should be added
   --  @param Why3_Type_Name Name to be used in Why for the type
   --  @param Und_Ent The entity of the array type to be translated. It should
   --                 be either an unconstrained array type or a dynamically
   --                 constrained array type.

   --  The following two procedures take an array [Args] and an index [Arg_Ind]
   --  as in-out parameters. They fill the array with a number of parameters,
   --  starting from the initial value of [Arg_Ind], and set the final value
   --  of [Arg_Ind] to the index after the last written value.

   function Get_Array_Attr
     (Domain : EW_Domain;
      Item   : Item_Type;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id;
   --  Get the expression for the attribute (first/last/length) of an array
   --  item.
   --  @param Domain the domain of the returned expression
   --  @param Item the item for the array object
   --  @param Attr the querried array attribute
   --  @param Dim dimension of the attribute
   --  @param Typ expected type of the result. It is only relevant for
   --         length attribute.
   --  @return the translated array attribute into Why3

   function Prepare_Indices_Substitutions
     (Section     : W_Section_Id;
      Typ         : Entity_Id;
      Prefix      : String;
      Declare_One : Boolean := True) return W_Clone_Substitution_Array;
   --  @param Typ The representation type of the index
   --  @param Prefix The prefix of the current index ("I1" e.g.)
   --  @param Declare_One specify if the function one of the index should be
   --         declared or not : to be set to false if this function has
   --         allready been called for the current module.
   --  @return the substitution array for cloning the indice module of
   --          _gnatprove_standard.mlw

   function Prepare_Standard_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @return An array of substitutions for cloning the module
   --          Standard_Array_Logical_Ax.

   function Prepare_Subtype_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @return An array of substitutions for cloning the module
   --          Subtype_Array_Logical_Ax.

   procedure Declare_Additional_Symbols (E       : Entity_Id;
                                         Section : W_Section_Id);
   --  @param E Entity of the one dimensional array type.
   --  @return Declares logical operators and comparison function when
   --          necessary.

   -----------------
   -- Add_Map_Arg --
   -----------------

   procedure Add_Map_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Arg_Ind : in out Positive)
   is
      W_Ty : constant W_Type_Id := Get_Type (Expr);
      Ty   : constant Entity_Id := Get_Ada_Node (+W_Ty);
   begin
      if Has_Static_Array_Type (Ty)
        or else Get_Type_Kind (W_Ty) = EW_Split
      then
         Args (Arg_Ind) := Expr;
      else
         Args (Arg_Ind) :=
           New_Call
             (Domain => Domain,
              Name   => E_Symb (Ty, WNE_To_Array),
              Args => (1 => Expr));
      end if;
      Arg_Ind := Arg_Ind + 1;
   end Add_Map_Arg;

   ------------------
   -- Add_Attr_Arg --
   ------------------

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive)
   is
   begin
      Args (Arg_Ind) :=
        Insert_Conversion_To_Rep_No_Bool
          (Domain,
           Get_Array_Attr (Domain, Expr, Attr, Dim));
      Arg_Ind := Arg_Ind + 1;
   end Add_Attr_Arg;

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive)
   is
   begin
      Args (Arg_Ind) :=
        Insert_Conversion_To_Rep_No_Bool
          (Domain,
           Get_Array_Attr (Domain, Ty, Attr, Dim));
      Arg_Ind := Arg_Ind + 1;
   end Add_Attr_Arg;

   -------------------
   -- Add_Array_Arg --
   -------------------

   procedure Add_Array_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Arg_Ind : in out Positive)
   is
      W_Ty : constant W_Type_Id := Get_Type (Expr);
      Ty   : constant Entity_Id := Get_Ada_Node (+W_Ty);
      Dim  : constant Positive := Positive (Number_Dimensions (Ty));
   begin
      Add_Map_Arg (Domain, Args, Expr, Arg_Ind);
      for I in 1 .. Dim loop
         Add_Attr_Arg (Domain, Args, Expr, Attribute_First, I, Arg_Ind);
         Add_Attr_Arg (Domain, Args, Expr, Attribute_Last, I, Arg_Ind);
      end loop;
   end Add_Array_Arg;

   -----------------------------
   -- Array_Convert_From_Base --
   -----------------------------

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ar     : W_Expr_Id) return W_Expr_Id
   is
      Ty     : constant W_Type_Id := Get_Type (Ar);
      Ty_Ent : constant Entity_Id := Get_Ada_Node (+Ty);
      Len    : constant Integer :=
        1 + 2 * Integer (Number_Dimensions (Ty_Ent));
      Args   : W_Expr_Array (1 .. Len);
      Count  : Positive := 1;
   begin
      Add_Array_Arg (Domain, Args, Ar, Count);
      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (Ty_Ent, WNE_Of_Array),
           Args   => Args,
           Typ    => EW_Abstract (Ty_Ent));
   end Array_Convert_From_Base;

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Target : Entity_Id;
      Ar     : W_Expr_Id;
      First  : W_Expr_Id;
      Last   : W_Expr_Id) return W_Expr_Id
   is
      First_Int : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain, Expr => First);

      Last_Int  : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain, Expr => Last);

   begin
      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (Target, WNE_Of_Array),
           Args   => (1 => Ar, 2 => First_Int, 3 => Last_Int),
           Typ    => EW_Abstract (Target));
   end Array_Convert_From_Base;

   function Array_Convert_From_Base
     (Domain   : EW_Domain;
      Old_Ar   : W_Expr_Id;
      New_Base : W_Expr_Id) return W_Expr_Id
   is
      Ty     : constant W_Type_Id := Get_Type (New_Base);
      Ty_Ent : constant Entity_Id := Get_Ada_Node (+Ty);
      Len    : constant Integer :=
        1 + 2 * Integer (Number_Dimensions (Ty_Ent));
      Args   : W_Expr_Array (1 .. Len);
      Count  : Positive := 1;
   begin
      Add_Array_Arg (Domain, Args, Old_Ar, Count);
      Args (1) := New_Base;
      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (Ty_Ent, WNE_Of_Array),
           Args   => Args,
           Typ    => EW_Abstract (Ty_Ent));
   end Array_Convert_From_Base;

   ---------------------------
   -- Array_Convert_To_Base --
   ---------------------------

   function Array_Convert_To_Base
     (Domain : EW_Domain;
      Ar     : W_Expr_Id) return W_Expr_Id
   is
      Ty     : constant W_Type_Id := Get_Type (Ar);
      Ty_Ent : constant Entity_Id := Get_Ada_Node (+Ty);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (Ty_Ent, WNE_To_Array),
           Args   => (1 => +Ar),
           Typ    => EW_Split (Ty_Ent));
   end Array_Convert_To_Base;

   -----------------------
   -- Build_Length_Expr --
   -----------------------

   function Build_Length_Expr
     (Domain      : EW_Domain;
      First, Last : W_Expr_Id;
      Typ         : W_Type_Id := EW_Int_Type) return W_Expr_Id
   is
      First_Rep : constant W_Expr_Id :=
        Insert_Scalar_Conversion (Domain, Empty, First, Typ);
      Last_Rep  : constant W_Expr_Id :=
        Insert_Scalar_Conversion (Domain, Empty, Last, Typ);
      Cond      : constant W_Expr_Id :=
        New_Call
          (Domain => Domain,
           Name   => (if Typ = EW_Int_Type
                      then Int_Infix_Le
                      elsif Why_Type_Is_BitVector (Typ)
                      then MF_BVs (Typ).Ule
                      else raise Program_Error),
           Typ    => EW_Bool_Type,
           Args   => (+First_Rep, +Last_Rep));
      Len       : constant W_Expr_Id :=
        New_Discrete_Add
          (Domain,
           New_Discrete_Substract (Domain, Last_Rep, First_Rep),
           New_Discrete_Constant (Value => Uint_1,
                                  Typ   => Typ));
   begin
      return
        New_Conditional
          (Domain    => Domain,
           Condition => Cond,
           Then_Part => Len,
           Else_Part => New_Discrete_Constant (Value => Uint_0,
                                               Typ   => Typ),
           Typ       => Typ);
   end Build_Length_Expr;

   function Build_Length_Expr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id is
   begin
      return
        Build_Length_Expr
          (Domain,
           Get_Array_Attr (Domain, Expr, Attribute_First, Dim),
           Get_Array_Attr (Domain, Expr, Attribute_Last, Dim),
           Typ);
   end Build_Length_Expr;

   function Build_Length_Expr
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id is
   begin
      return
        Build_Length_Expr
          (Domain,
           Get_Array_Attr (Domain, Ty, Attribute_First, Dim),
           Get_Array_Attr (Domain, Ty, Attribute_Last, Dim),
           Typ);
   end Build_Length_Expr;

   -----------------------
   -- Declare_Ada_Array --
   -----------------------

   procedure Declare_Ada_Array
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Why_Name : constant W_Name_Id := To_Why_Type (E, Local => True);
   begin
      if Is_Static_Array_Type (E) then
         Declare_Constrained (File, E);
      else
         Declare_Unconstrained (File, Why_Name, E);
      end if;
   end Declare_Ada_Array;

   --------------------------------
   -- Declare_Additional_Symbols --
   --------------------------------

   procedure Declare_Additional_Symbols
     (E       : Entity_Id;
      Section : W_Section_Id) is
   begin
      if Has_Discrete_Type (Component_Type (E)) then

         --  For discrete arrays of dimension 1 we need the to_int function on
         --  component_type to define the comparison functions.
         --  We clone a specific module Array_Comparison_Axiom which needs an
         --  additional parameter to_rep.

         declare
            Base : constant W_Type_Id :=
              Base_Why_Type_No_Bool (Component_Type (E));

            Fst_Idx : constant Node_Id :=
              First_Index (if Ekind (E) = E_String_Literal_Subtype
                           then Retysp (Etype (E))
                           else E);

            Sbst : constant W_Clone_Substitution_Array :=
              (1 => New_Clone_Substitution
                 (Kind      => EW_Type_Subst,
                  Orig_Name => To_Name (WNE_Array_Component_Type),
                  Image     => To_Name (WNE_Array_Component_Type)),
               2 =>
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name (Symbol => NID ("to_rep")),
                    Image     =>
                      Get_Name
                        (Conversion_Name
                           (From => EW_Abstract (Component_Type (E)),
                            To   => Base))),
               3 =>
                 New_Clone_Substitution
                   (Kind      => EW_Type_Subst,
                    Orig_Name => New_Name (Symbol => NID ("map")),
                    Image     => New_Name (Symbol => NID ("map"))))
              &
              Prepare_Indices_Substitutions
              (Section, Base_Type (Etype (Fst_Idx)), "Index")
              &
              (1 =>
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name (Symbol => NID ("get")),
                    Image     => New_Name (Symbol => NID ("get"))),
               2 =>
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name (Symbol => NID ("bool_eq")),
                    Image     => New_Name (Symbol => NID ("bool_eq"))));

         begin
            if Has_Modular_Integer_Type (Component_Type (E)) then
               Emit (Section,
                     New_Clone_Declaration
                       (Theory_Kind   => EW_Module,
                        Clone_Kind    => EW_Export,
                        Origin        =>
                          (if Base = EW_BitVector_8_Type then
                             Array_BV8_Rep_Comparison_Ax
                           elsif Base = EW_BitVector_16_Type then
                             Array_BV16_Rep_Comparison_Ax
                           elsif Base = EW_BitVector_32_Type then
                             Array_BV32_Rep_Comparison_Ax
                           elsif Base = EW_BitVector_64_Type then
                             Array_BV64_Rep_Comparison_Ax
                           else raise Program_Error),
                        As_Name       => No_Name,
                        Substitutions => Sbst));
            else
               Emit (Section,
                     New_Clone_Declaration
                       (Theory_Kind   => EW_Module,
                        Clone_Kind    => EW_Export,
                        Origin        => Array_Int_Rep_Comparison_Ax,
                        As_Name       => No_Name,
                        Substitutions => Sbst));
            end if;
         end;
      end if;

      if Has_Boolean_Type (Component_Type (E)) then

         --  For arrays of boolean types of dimension 1 we need to define the
         --  logical operators.

         if Is_Standard_Boolean_Type (Component_Type (E)) then

            --  For Boolean, use the module Standard_Array_Logical_Op_Axioms

            Emit (Section,
                  New_Clone_Declaration
                    (Theory_Kind   => EW_Module,
                     Clone_Kind    => EW_Export,
                     Origin        => Standard_Array_Logical_Ax,
                     As_Name       => No_Name,
                     Substitutions =>
                       Prepare_Standard_Array_Logical_Substitutions
                         (Section, E)));
         else

            --  We clone a specific module Subtype_Array_Logical_Op_Axioms
            --  which needs an additional parameter to_int.

            Emit (Section,
                  New_Clone_Declaration
                    (Theory_Kind   => EW_Module,
                     Clone_Kind    => EW_Export,
                     Origin        => Subtype_Array_Logical_Ax,
                     As_Name       => No_Name,
                     Substitutions =>
                       Prepare_Subtype_Array_Logical_Substitutions
                         (Section, E)));
         end if;
      end if;
   end Declare_Additional_Symbols;

   -----------------------------------
   -- Prepare_Indices_Substitutions --
   -----------------------------------

   function Prepare_Indices_Substitutions
     (Section     : W_Section_Id;
      Typ         : Entity_Id;
      Prefix      : String;
      Declare_One : Boolean := True) return W_Clone_Substitution_Array
   is
      WTyp   : constant W_Type_Id := Base_Why_Type_No_Bool (Base_Type (Typ));
      One_Id : constant W_Identifier_Id :=
        New_Identifier (Name => "index_" & Prefix & "_one");

   begin
      if Declare_One then
         Emit (Section,
               Why.Gen.Binders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => One_Id,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Binders     => (1 .. 0 => <>),
                  Def         =>
                    (if Is_Modular_Integer_Type (Typ) then
                       New_Modular_Constant (Value => Uint_1,
                                             Typ   => WTyp)
                     else
                       New_Integer_Constant (Value => Uint_1)),
                  Return_Type => WTyp));
      end if;

      --  ??? after Johannes refacto of names use this mecanism to print the
      --  new operators instead of NIDs.

      return (1 => New_Clone_Substitution
              (Kind      => EW_Type_Subst,
               Orig_Name => New_Name (Symbol => NID (Prefix & ".t")),
               Image     => Get_Name (WTyp)),
              2 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".le")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ule
                    else
                      Int_Infix_Le)),
              3 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".lt")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ult
                    else
                      Int_Infix_Lt)),
              4 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".gt")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ugt
                    else
                      Int_Infix_Gt)),
              5 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".add")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Add
                    else
                      Int_Infix_Add)),
              6 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".sub")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Sub
                    else
                      Int_Infix_Subtr)),
              7 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symbol => NID (Prefix & ".one")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).One
                    else
                      One_Id)));
   end Prepare_Indices_Substitutions;

   --------------------------------------------------
   -- Prepare_Standard_Array_Logical_Substitutions --
   --------------------------------------------------

   function Prepare_Standard_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id)
      return W_Clone_Substitution_Array
   is
     ((1 =>
          New_Clone_Substitution
         (Kind      => EW_Type_Subst,
          Orig_Name => New_Name (Symbol => NID ("map")),
          Image     => New_Name (Symbol => NID ("map"))),
       2 =>
          New_Clone_Substitution
         (Kind      => EW_Function,
          Orig_Name => New_Name (Symbol => NID ("get")),
          Image     => New_Name (Symbol => NID ("get"))))
      & Prepare_Indices_Substitutions
        (Section, Etype (First_Index (Und_Ent)), "Index",
         False));

   -------------------------------------------------
   -- Prepare_Subtype_Array_Logical_Substitutions --
   -------------------------------------------------

   function Prepare_Subtype_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id)
      return W_Clone_Substitution_Array
   is
     (Prepare_Standard_Array_Logical_Substitutions (Section, Und_Ent)
      & (1 =>
              New_Clone_Substitution
           (Kind      => EW_Type_Subst,
            Orig_Name => To_Name (WNE_Array_Component_Type),
            Image     => To_Name (WNE_Array_Component_Type)),
         2 =>
            New_Clone_Substitution
           (Kind      => EW_Function,
            Orig_Name => New_Name (Symbol => NID ("to_int")),
            Image     =>
               Get_Name (Conversion_Name
                         (From =>
                             +EW_Abstract (Component_Type (Und_Ent)),
                          To   => +EW_Int_Type))),
         3 =>
            New_Clone_Substitution
           (Kind      => EW_Function,
            Orig_Name => New_Name (Symbol => NID ("of_int")),
            Image     =>
               Get_Name (Conversion_Name
                         (From => +EW_Int_Type,
                          To   =>
                             +EW_Abstract (Component_Type (Und_Ent)))))));

   ----------------
   -- Append_Num --
   ----------------

   function Append_Num (S : String; Count : Positive) return String is
     (if Count = 1 then S else S & "_" & Image (Count, 1));

   -------------------------
   -- Declare_Constrained --
   -------------------------

   procedure Declare_Constrained
     (Section : W_Section_Id;
      Und_Ent : Entity_Id)
   is
      Dimension       : constant Pos := Number_Dimensions (Und_Ent);
      Index           : Entity_Id := First_Index (Und_Ent);
      Subst_Per_Index : constant Int := 3;
      Subst           : W_Clone_Substitution_Array
        (1 .. Integer (Dimension * Subst_Per_Index) + 2);
      Cursor          : Integer := 1;
      Clone           : constant W_Module_Id :=
        Constr_Arrays (Positive (Dimension));
      Array_Theory    : constant W_Module_Id :=
        Get_Array_Theory (Und_Ent).Module;

      procedure Declare_Attribute
        (Kind      : Why_Name_Enum;
         Value     : Uint;
         Typ       : W_Type_Id);
      --  ???

      -----------------------
      -- Declare_Attribute --
      -----------------------

      procedure Declare_Attribute
        (Kind  : Why_Name_Enum;
         Value : Uint;
         Typ   : W_Type_Id)
      is
         Attr_Name : constant W_Name_Id := To_Local (E_Symb (Und_Ent, Kind));
      begin
            Emit (Section,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => New_Identifier (Attr_Name),
                     Binders     => (1 .. 0 => <>),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => Typ,
                     Def         => New_Discrete_Constant
                       (Value =>  Value,
                        Typ   => Typ)));
         Subst (Cursor) :=
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => Attr_Name,
              Image     => Attr_Name);
         Cursor := Cursor + 1;
      end Declare_Attribute;

   --  Start of processing for Declare_Constrained

   begin

      Emit (Section,
            New_Type_Decl (Name => To_Name (WNE_Array_Component_Type),
                           Alias => EW_Abstract (Component_Type (Und_Ent))));

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => New_Name (Symbol => NID ("map")),
           Image     => New_Name (Symbol => NID ("map"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Function,
           Orig_Name => New_Name (Symbol => NID ("array_bool_eq")),
           Image     => New_Name (Symbol => NID ("bool_eq"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      if Ekind (Und_Ent) = E_String_Literal_Subtype then
         pragma Assert (Has_Array_Type (Etype (Und_Ent)) and then
                        Ekind (Etype (Und_Ent)) /= E_String_Literal_Subtype);
         declare
            Low  : constant Uint :=
              Expr_Value (String_Literal_Low_Bound (Und_Ent));
            R_Ty : constant W_Type_Id := Base_Why_Type_No_Bool
              (Base_Type (Retysp (Etype (
               First_Index (Retysp (Etype (Und_Ent)))))));
         begin
            Declare_Attribute (WNE_Attr_First (1), Low, R_Ty);
            Declare_Attribute (WNE_Attr_Last (1),
                               String_Literal_Length (Und_Ent) - Low + 1,
                               R_Ty);

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name
                   (Symbol => NID
                      (Append_Num ("index_rep_type", 1))),
                 Image     => Get_Name (R_Ty));
            Cursor := Cursor + 1;
         end;
      else
         declare
            Count : Positive := 1;
         begin
            while Present (Index) loop
               declare
                  Rng  : constant Node_Id := Get_Range (Index);
                  R_Ty : constant W_Type_Id := Base_Why_Type_No_Bool
                    (Base_Type (Retysp (Etype (Index))));
               begin
                  Declare_Attribute (WNE_Attr_First (Count),
                                     Expr_Value (Low_Bound (Rng)),
                                     R_Ty);
                  Declare_Attribute (WNE_Attr_Last (Count),
                                     Expr_Value (High_Bound (Rng)),
                                     R_Ty);

                  Subst (Cursor) :=
                    New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name => New_Name
                         (Symbol => NID
                            (Append_Num ("index_rep_type", Count))),
                       Image     => Get_Name (R_Ty));
                  Cursor := Cursor + 1;

                  Count := Count + 1;
                  Next_Index (Index);
               end;
            end loop;
         end;
      end if;

      Emit (Section,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               As_Name       => No_Name,
               Origin        => Clone,
               Substitutions => Subst));
   end Declare_Constrained;

   ---------------------------
   -- Declare_Unconstrained --
   ---------------------------

   procedure Declare_Unconstrained
     (Section        : W_Section_Id;
      Why3_Type_Name : W_Name_Id;
      Und_Ent        : Entity_Id)
   is
      Dimension       : constant Pos := Number_Dimensions (Und_Ent);
      Subst_Per_Index : constant Int := 7;
      Subst           : W_Clone_Substitution_Array
        (1 .. Integer (Dimension * Subst_Per_Index) + 2);
      Cursor          : Integer := 1;
      Index           : Node_Id := First_Index (Und_Ent);
      Dim_Count       : Integer := 1;
      Clone           : constant W_Module_Id :=
        Unconstr_Arrays (Positive (Dimension));
      Array_Theory    : constant W_Module_Id :=
        Get_Array_Theory (Und_Ent).Module;

   begin
      Emit (Section,
            New_Type_Decl (Name => To_Name (WNE_Array_Component_Type),
                           Alias => EW_Abstract (Component_Type (Und_Ent))));

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => New_Name (Symbol => NID ("map")),
           Image     => New_Name (Symbol => NID ("map"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Function,
           Orig_Name => New_Name (Symbol => NID ("array_bool_eq")),
           Image     => New_Name (Symbol => NID ("bool_eq"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      while Present (Index) loop
         declare
            Ind_Ty : constant Entity_Id := Etype (Index);
            B_Ty   : constant Entity_Id := Base_Type (Ind_Ty);
            B_Type : constant W_Type_Id := +EW_Abstract (B_Ty);
            R_Ty   : constant W_Type_Id := Base_Why_Type_No_Bool (B_Ty);
         begin
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name
                   (Symbol => NID (Append_Num ("index_base_type", Dim_Count))),
                 Image     => Ident_Of_Ada_Type (B_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name
                   (Symbol => NID (Append_Num ("index_rep_type", Dim_Count))),
                 Image     => Get_Name (R_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name
                   (Symbol => NID (Append_Num ("to_rep", Dim_Count))),
                 Image     =>
                   Get_Name (Conversion_Name (From => +B_Type,
                                             To => R_Ty)));
            Cursor := Cursor + 1;

            if R_Ty = EW_Int_Type then
               declare
                  Id_Id : constant W_Identifier_Id :=
                    New_Identifier (Name =>
                                      "index_" & Image (Dim_Count, 1) & "_id");
                  X_Id : constant W_Identifier_Id :=
                    New_Identifier (Name => "x", Typ => R_Ty);
               begin
                  Emit (Section,
                        Why.Gen.Binders.New_Function_Decl
                          (Domain  => EW_Term,
                           Name    => Id_Id,
                           Binders =>
                             (1 => (B_Name => X_Id, others => <>)),
                           Labels  => Name_Id_Sets.Empty_Set,
                           Def     => +X_Id,
                           Return_Type => R_Ty));

                  Subst (Cursor) :=
                    New_Clone_Substitution
                      (Kind      => EW_Function,
                       Orig_Name => New_Name
                         (Symbol => NID
                            (Append_Num ("rep_to_int", Dim_Count))),
                       Image     => Get_Name (Id_Id));
               end;
            else
               Subst (Cursor) :=
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name
                      (Symbol => NID (Append_Num ("rep_to_int", Dim_Count))),
                    Image     =>
                      Get_Name (Conversion_Name (From => R_Ty,
                                                To => EW_Int_Type)));
            end if;
            Cursor := Cursor + 1;

            --  Range on base type only used for empty array (e.g. 12..7)
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name =>
                   To_Local
                     (E_Symb (Und_Ent, WNE_Array_Base_Range_Pred (Dim_Count))),
                 Image     =>
                    Get_Name (Range_Pred_Name (B_Ty)));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name =>
                   To_Local (E_Symb (Und_Ent,
                     WNE_Index_Dynamic_Property (Dim_Count))),
                 Image     =>
                       Get_Name (Dynamic_Prop_Name (Ind_Ty)));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name
                   (Symbol => NID (Append_Num ("index_rep_le", Dim_Count))),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Ind_Ty) then
                         MF_BVs (R_Ty).Ule
                    else
                       Int_Infix_Le));
            Cursor := Cursor + 1;
         end;
         Dim_Count := Dim_Count + 1;
         Next_Index (Index);
      end loop;

      Emit (Section,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               As_Name       => No_Name,
               Origin        => Clone,
               Substitutions => Subst));
      --  Declare the abstract type of the unconstrained array and mark
      --  function "to_array" as projection (from this type to why3 map type)
      Emit (Section,
            New_Type_Decl
              (Why3_Type_Name,
               Alias =>
                 New_Named_Type (To_String (WNE_Array_Type))));
      Emit_Projection_Metas (Section, "to_array");
      Emit_Projection_Metas (Section, "first");
      Emit_Projection_Metas (Section, "last");
      --  Dim_Count is actually nb of dimention + 1 here
      for I in 2 .. Dim_Count - 1 loop
         Emit_Projection_Metas (Section, "first_" & Image (I, 1));
         Emit_Projection_Metas (Section, "last_"  & Image (I, 1));
      end loop;

      if Und_Ent = Standard_String then
         declare
            Dummy_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "x", Typ => M_Main.String_Image_Type);
            Str_Typ     : constant W_Type_Id :=
              New_Named_Type (Name => Why3_Type_Name);
            Dummy_Ident2 : constant W_Identifier_Id :=
              New_Identifier (Name => "x", Typ => Str_Typ);
         begin
            Emit (Section,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (To_String_Id),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                          Ada_Node => Empty,
                          Mutable  => False,
                          B_Ent    => Null_Entity_Name,
                          B_Name   => Dummy_Ident)),
                     Return_Type => Str_Typ));
            Emit (Section,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (Of_String_Id),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                          Ada_Node => Empty,
                          Mutable  => False,
                          B_Ent    => Null_Entity_Name,
                          B_Name   => Dummy_Ident2)),
                     Return_Type => M_Main.String_Image_Type));
         end;
      end if;
   end Declare_Unconstrained;

   --------------------
   -- Get_Array_Attr --
   --------------------

   function Get_Array_Attr
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Params : Transformation_Params := Body_Params;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id is
   begin

      if Attr in Attribute_First | Attribute_Last then
         declare
            Index_Type : constant Entity_Id := Nth_Index_Type (Ty, Dim);
         begin
            return Insert_Simple_Conversion
              (Domain => EW_Term,
               Expr   => New_Attribute_Expr (Ty     => Index_Type,
                                             Domain => Domain,
                                             Attr   => Attr,
                                             Params => Params),
               To     => Nth_Index_Rep_Type_No_Bool (Ty, Dim));
         end;
      elsif Is_Static_Array_Type (Ty) then
         pragma Assert (Is_Constrained (Ty));
         return
           New_Discrete_Constant (Value => Static_Array_Length (Ty, Dim),
                                  Typ   => Typ);
      else
         pragma Assert (Is_Constrained (Ty));
         return Build_Length_Expr (Domain, Ty, Dim, Typ);
      end if;
   end Get_Array_Attr;

   function Get_Array_Attr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id
   is
      W_Ty : constant W_Type_Id := Get_Type (Expr);
      Ty   : constant Entity_Id := Get_Ada_Node (+W_Ty);
   begin

      --  If the type is constrained, just use the type information

      if Is_Static_Array_Type (Ty) then
         return Get_Array_Attr (Domain, Ty, Attr, Dim, Typ => Typ);

      --  if the object is a split object, look up the required expressions in
      --  the symbol table

      elsif Get_Type_Kind (W_Ty) = EW_Split then
         return Get_Array_Attr (Domain,
                                Ada_Ent_To_Why.Element
                                  (Symbol_Table,
                                   Get_Entity_Of_Variable (Expr)),
                                Attr,
                                Dim,
                                Typ);
      else

         if Attr in Attribute_First | Attribute_Last then
            declare
               Enum : constant Why_Name_Enum :=
                 (case Attr is
                     when Attribute_First => WNE_Attr_First (Dim),
                     when Attribute_Last  => WNE_Attr_Last (Dim),
                     when others          => raise Program_Error);
            begin
               return
                 New_Call
                   (Domain => Domain,
                    Name   => E_Symb (Ty, Enum),
                    Args   => (1 => Expr),
                    Typ    => Nth_Index_Rep_Type_No_Bool (Ty, Dim));
            end;
         elsif Typ = EW_Int_Type then
            return
              New_Call
                (Domain => Domain,
                 Name   => E_Symb (Ty, WNE_Attr_Length (Dim)),
                 Args   => (1 => Expr),
                 Typ    => EW_Int_Type);
         else
            return
              Build_Length_Expr (Domain => Domain,
                                 Expr   => Expr,
                                 Dim    => Dim,
                                 Typ    => Typ);
         end if;
      end if;
   end Get_Array_Attr;

   function Get_Array_Attr
     (Domain : EW_Domain;
      Item   : Item_Type;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Typ    : W_Type_Id := EW_Int_Type) return W_Expr_Id
   is
   begin
      case Attr is
         when Attribute_First =>
            return +Item.Bounds (Dim).First;
         when Attribute_Last =>
            return +Item.Bounds (Dim).Last;
         when Attribute_Length =>
            return
              Build_Length_Expr
                (Domain => Domain,
                 First  => +Item.Bounds (Dim).First,
                 Last   => +Item.Bounds (Dim).Last,
                 Typ    => Typ);
         when others =>
            raise Program_Error;
      end case;
   end Get_Array_Attr;

   ----------------------------
   -- Get_Entity_Of_Variable --
   ----------------------------

   function Get_Entity_Of_Variable (E : W_Expr_Id) return Entity_Id is
   begin
      pragma Assert (Get_Kind (+E) in W_Identifier | W_Deref | W_Tagged);

      case Get_Kind (+E) is
         when W_Identifier =>
            return Get_Ada_Node (+E);

         when W_Deref =>
            declare
               Id : constant W_Identifier_Id := Get_Right (+E);
            begin
               return Get_Ada_Node (+Id);
            end;

         when W_Tagged =>
            declare
               Expr : constant W_Expr_Id := Get_Def (W_Tagged_Id (E));
            begin
               return Get_Entity_Of_Variable (Expr);
            end;

         when others =>
            raise Program_Error;
      end case;
   end Get_Entity_Of_Variable;

   ----------------------
   -- New_Array_Access --
   ----------------------

   function New_Array_Access
     (Ada_Node  : Node_Id;
      Ar        : W_Expr_Id;
      Index     : W_Expr_Array;
      Domain    : EW_Domain) return W_Expr_Id
   is
      Why_Ty    : constant W_Type_Id := Get_Type (Ar);
      Ty_Entity : constant Entity_Id := Get_Ada_Node (+Why_Ty);
      Name      : constant W_Identifier_Id :=
        Get_Array_Theory (Ty_Entity).Get;
      Elts     : W_Expr_Id;
      Ret_Ty   : constant W_Type_Id :=
        EW_Abstract (Component_Type (Unique_Entity (Ty_Entity)));

   begin
      if Is_Static_Array_Type (Ty_Entity) or else
        Get_Type_Kind (Why_Ty) = EW_Split
      then
         Elts := Ar;
      else
         Elts := Array_Convert_To_Base (Domain, Ar);
      end if;

      return
        New_Call
        (Ada_Node => Ada_Node,
         Name     => Name,
         Domain   => Domain,
         Args     => (1 => Elts) & Index,
         Typ      => Ret_Ty);
   end New_Array_Access;

   --------------------------
   -- New_Array_Range_Expr --
   --------------------------

   function New_Array_Range_Expr
     (Index_Expr : W_Expr_Id;
      Array_Expr : W_Expr_Id;
      Domain     : EW_Domain;
      Dim        : Positive)
     return W_Expr_Id
   is
   begin
      return New_Range_Expr
             (Domain => Domain,
              Low    => Insert_Conversion_To_Rep_No_Bool
                (Prog_Or_Term_Domain (Domain),
                 Get_Array_Attr (Domain => Prog_Or_Term_Domain (Domain),
                                 Expr   => Array_Expr,
                                 Attr   => Attribute_First,
                                 Dim    => Dim)),
              High   => Insert_Conversion_To_Rep_No_Bool
                (Prog_Or_Term_Domain (Domain),
                 Get_Array_Attr (Domain => Prog_Or_Term_Domain (Domain),
                                 Expr   => Array_Expr,
                                 Attr   => Attribute_Last,
                                 Dim    => Dim)),
              Expr   => Insert_Conversion_To_Rep_No_Bool
                (Prog_Or_Term_Domain (Domain),
                 Index_Expr));
   end New_Array_Range_Expr;

   ----------------------
   -- New_Array_Update --
   ----------------------

   function New_Array_Update
     (Ada_Node : Node_Id;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Value    : W_Expr_Id;
      Domain   : EW_Domain) return W_Expr_Id
   is
      W_Ty      : constant W_Type_Id := Get_Type (Ar);
      Ty_Entity : constant Entity_Id := Get_Ada_Node (+W_Ty);
      Name      : constant W_Identifier_Id :=
        Get_Array_Theory (Ty_Entity).Set;
   begin
      if Is_Static_Array_Type (Ty_Entity)
        or else Get_Type_Kind (W_Ty) = EW_Split
      then
         return
           New_Call
             (Ada_Node => Ada_Node,
              Domain   => Domain,
              Name     => Name,
              Args     => (1 => +Ar) & Index & (1 => +Value),
              Typ      => W_Ty);
      else
         declare
            Args      : constant W_Expr_Array :=
              (1 => New_Call
                 (Domain => Domain,
                  Name   => E_Symb (Ty_Entity, WNE_To_Array),
                  Args   => (1 => +Ar)))
              & Index & (1 => +Value);
            Array_Upd : constant W_Expr_Id :=
              New_Call
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Name     => Name,
                 Args     => Args,
                 Typ      => W_Ty);
         begin
            return
              New_Record_Update
                (Name    => Ar,
                 Updates =>
                   (1 =>
                      New_Field_Association
                        (Domain => Domain,
                         Field  => E_Symb (Ty_Entity, WNE_Array_Elts),
                         Value  => Array_Upd)),
                 Typ     => W_Ty);
         end;
      end if;
   end New_Array_Update;

   --------------------------
   -- NNew_Bounds_Equality --
   --------------------------

   function New_Bounds_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Dim       : Positive) return W_Pred_Id
   is
      Result : W_Expr_Id := +True_Pred;
   begin
      for I in 1 .. Dim loop
         Result :=
           New_And_Expr
             (Conjuncts =>
                (1 => Result,

                 --  <left_arr>.first__I = <right_arr>.first__I

                 2 => New_Comparison
                   (Symbol => Why_Eq,
                    Left   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    Right  => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Right_Arr,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    Domain => EW_Pred),

                 --  <left_arr>.last__I = <right_arr>.last__I

                 3 => New_Comparison
                   (Symbol => Why_Eq,
                    Left   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    Right  => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Right_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    Domain => EW_Pred)),
              Domain    => EW_Pred);
      end loop;

      return +Result;
   end New_Bounds_Equality;

   ---------------------
   -- New_Concat_Call --
   ---------------------

   function New_Concat_Call
     (Domain : EW_Domain;
      Args   : W_Expr_Array;
      Typ    : W_Type_Id) return W_Expr_Id is
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Get_Array_Theory_1 (Get_Ada_Node (+Typ)).Concat,
           Args   => Args,
           Typ    => Typ);
   end New_Concat_Call;

   ---------------------------
   --  New_Dynamic_Property --
   ---------------------------

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Args   : W_Expr_Array;
      Params : Transformation_Params := Body_Params) return W_Expr_Id
   is
      Dim       : constant Positive := Positive (Number_Dimensions (Ty));
      Call_Args : W_Expr_Array (1 .. 4 * Dim);

   begin
      pragma Assert (Args'Length = 2 * Dim);
      for Count in 0 .. Dim - 1 loop
         declare
            W_Typ      : constant W_Type_Id :=
              Nth_Index_Rep_Type_No_Bool (E   => Ty,
                                          Dim => Count + 1);
            First_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Get_Array_Attr
                                          (Domain => Domain,
                                           Ty     => Ty,
                                           Attr   => Attribute_First,
                                           Dim    => Count + 1,
                                           Params => Params),
                                        To     => W_Typ);
            Last_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Get_Array_Attr
                                          (Domain => Domain,
                                           Ty     => Ty,
                                           Attr   => Attribute_Last,
                                           Dim    => Count + 1,
                                           Params => Params),
                                        To     => W_Typ);
            F_Expr    : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Args (2 * Count + 1),
                                        To     => W_Typ);
            L_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Args (2 * Count + 2),
                                        To     => W_Typ);
         begin
            Call_Args (4 * Count + 1) := First_Expr;
            Call_Args (4 * Count + 2) := Last_Expr;
            Call_Args (4 * Count + 3) := F_Expr;
            Call_Args (4 * Count + 4) := L_Expr;
         end;
      end loop;

      return New_Call (Domain => Domain,
                       Name   => Dynamic_Prop_Name (Ty),
                       Args   => Call_Args,
                       Typ    => EW_Bool_Type);
   end New_Dynamic_Property;

   ---------------------------
   --  New_Element_Equality --
   ---------------------------

   function New_Element_Equality
     (Ada_Node  : Node_Id := Empty;
      Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Index     : W_Expr_Array) return W_Pred_Id
   is
      Left   : constant W_Expr_Id :=
        New_Array_Access
          (Ada_Node => Ada_Node,
           Domain   => EW_Term,
           Ar       => Left_Arr,
           Index    => Index);
      Right  : constant W_Expr_Id :=
        New_Array_Access
          (Ada_Node => Ada_Node,
           Domain   => EW_Term,
           Ar       => Right_Arr,
           Index    => Index);
      Result : constant W_Pred_Id :=
        +New_Comparison
          (Domain => EW_Pred,
           Symbol => Why_Eq,
           Left   => Left,
           Right  => Right);
   begin
      return Result;
   end New_Element_Equality;

   ------------------------
   -- New_Singleton_Call --
   ------------------------

   function New_Singleton_Call
     (Typ    : Node_Id;
      Domain : EW_Domain;
      Elt    : W_Expr_Id;
      Pos    : W_Expr_Id) return W_Expr_Id is
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => Get_Array_Theory_1 (Typ).Singleton,
           Args   => (1 => Elt, 2 => Pos));
   end New_Singleton_Call;

   ---------------------------
   -- Get_Array_Theory_Name --
   ---------------------------

   function Get_Array_Theory_Name (E : Entity_Id) return Name_Id is
      Name      : Unbounded_String := To_Unbounded_String ("Array_");
      Ty        : constant Entity_Id := Retysp (Etype (E));
      Type_Name : Unbounded_String;
      Index     : Node_Id := First_Index (Ty);
      Dim       : constant Positive :=
        Positive (Number_Dimensions (Ty));
   begin
      for I in 1 .. Dim loop
         if Has_Modular_Integer_Type (Etype (Index)) then
            Type_Name := To_Unbounded_String
              ("_BV" & Image (Integer (UI_To_Int (Esize (Etype (Index)))), 1));
         else
            Type_Name := To_Unbounded_String ("_Int");
         end if;

         Name := Name & Type_Name;

         Next_Index (Index);
      end loop;

      Type_Name := (To_Unbounded_String
                    ("__" &
                       Capitalize_First
                         (Full_Name (Retysp (Component_Type (Ty))))));
      Name := Name & Type_Name;

      return NID (To_String (Name));
   end Get_Array_Theory_Name;

   -------------------------------
   -- Build_Predicate_For_Array --
   -------------------------------

   function Build_Predicate_For_Array
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id
   is
      Ty_Ext     : constant Entity_Id := Retysp (Ty);
      Dim        : constant Positive :=
        Positive (Number_Dimensions (Ty_Ext));
      Vars       : Binder_Array (1 .. Dim);
      Indices    : W_Expr_Array (1 .. Dim);
      Range_Expr : W_Pred_Id := True_Pred;
      Index      : Node_Id := First_Index (Ty_Ext);
      I          : Positive := 1;
      T_Comp     : W_Expr_Id;
      Tmp        : W_Identifier_Id;
      Q_Expr     : W_Pred_Id;
      T          : W_Pred_Id := True_Pred;
   begin
      while Present (Index) loop
         Tmp := New_Temp_Identifier
           (Typ => Base_Why_Type_No_Bool (Index));
         Vars (I) := Binder_Type'(Ada_Node => Empty,
                                  B_Name   => Tmp,
                                  B_Ent    => Null_Entity_Name,
                                  Mutable  => False);
         Indices (I) := +Tmp;
         Range_Expr := +New_And_Expr
           (Left   => +Range_Expr,
            Right  => New_Array_Range_Expr (+Tmp, +Expr, EW_Pred, I),
            Domain => EW_Pred);
         Next_Index (Index);
         I := I + 1;
      end loop;

      pragma Assert (I = Indices'Last + 1);

      --  Call Build_Predicate_For_Comp on the array components.

      T_Comp :=
        +Build_Predicate_For_Comp
        (C_Expr => +New_Array_Access (Empty, +Expr, Indices, EW_Term),
         C_Ty   => Component_Type (Ty_Ext));

      if T_Comp /= +True_Pred then
         T_Comp := New_Conditional
           (Domain    => EW_Pred,
            Condition => +Range_Expr,
            Then_Part => T_Comp,
            Typ       => EW_Bool_Type);

         Q_Expr := New_Universal_Quantif
           (Binders => Vars,
            Pred    => +T_Comp);

         if T = True_Pred then
            T := Q_Expr;
         else
            T := +New_And_Then_Expr (Left   => +T,
                                     Right  => +Q_Expr,
                                     Domain => EW_Pred);
         end if;
      end if;
      return T;
   end Build_Predicate_For_Array;

   -----------------------------
   -- Create_Rep_Array_Theory --
   -----------------------------

   procedure Create_Rep_Array_Theory
     (File   : W_Section_Id;
      E      : Entity_Id;
      Name   : Name_Id;
      Module : out W_Module_Id);
   --  Create an Array theory
   --  @param File the current why file
   --  @param E the entity of type array
   --  @param Nam the name of the theory to be created, must be the one
   --         given by "Get_Array_Theory_Name"

   procedure Create_Rep_Array_Theory
     (File   : W_Section_Id;
      E      : Entity_Id;
      Name   : Name_Id;
      Module : out W_Module_Id)
   is
      Typ : constant Entity_Id := Retysp (Etype (E));

      Dim : constant Positive := Positive (Number_Dimensions (Typ));

      Subst : W_Clone_Substitution_Array (1 .. Dim * 7 + 1);
      --  ??? why 7

   begin
      Module := New_Module (File => No_Name,
                            Name => Name);

      Open_Theory
        (File, Module,
         Comment =>
           "Module for axiomatizing the array theory associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Start by generating all the substitutions for the theory(ies)
      --  Array__Index

      declare
         Index : Node_Id := First_Index (Typ);
      begin
         for I in 0 .. Dim - 1 loop

            Subst (I * 7 + 1 .. I * 7 + 7) := Prepare_Indices_Substitutions
              (File,
               Retysp (Etype (Index)),
               "I" & Image (I + 1, 1));

            Index := Next_Index (Index);

         end loop;
      end;

      --  Add the substitution for the component type

      Subst (Subst'Last) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => To_Name (WNE_Array_Component_Type),
           Image     => To_Name (WNE_Array_Component_Type));

      --  Declare the component type and clone the appropriate array theory.

      Emit (File,
            New_Type_Decl (Name  => To_Name (WNE_Array_Component_Type),
                           Alias => EW_Abstract (Component_Type (Typ))));

      Emit (File,
            New_Clone_Declaration
              (Theory_Kind   => EW_Theory,
               Clone_Kind    => EW_Export,
               Origin        => Array_Modules (Dim),
               As_Name       => No_Name,
               Substitutions => Subst));

      --  For arrays of dimension 1, we may need to clone additional modules
      --  containing definition for the comparison function (if the component
      --  type is discrete) or of boolean operators (if the component type is
      --  boolean).

      if Dim = 1 then
         Declare_Additional_Symbols (Typ, File);
      end if;

      Close_Theory (File, Kind => Definition_Theory);
   end Create_Rep_Array_Theory;

   ---------------------------------------
   -- Create_Rep_Array_Theory_If_Needed --
   ---------------------------------------

   procedure Create_Rep_Array_Theory_If_Needed
     (File          : W_Section_Id;
      E             : Entity_Id;
      Register_Only : Boolean := False)
   is
      Name   : constant Name_Id := Get_Array_Theory_Name (E);
      Module : W_Module_Id;

   begin
      if M_Arrays.Contains (Key => Name) then
         return;
      end if;

      --  If Name was inserted it means that the theory is not present:
      --  let's create it.

      if not Register_Only then
         Create_Rep_Array_Theory (File, E, Name, Module);
      else
         Module := New_Module (File => No_Name,
                               Name => Name);
      end if;

      --  Include the different parts of the declared module in the appropriate
      --  maps.

      M_Arrays.Include (Key      => Name,
                        New_Item => Init_Array_Module (Module));

      if Number_Dimensions (Retysp (Etype (E))) = 1 then
         M_Arrays_1.Include (Key      => Name,
                             New_Item => Init_Array_1_Module (Module));

         if Has_Boolean_Type (Component_Type (Retysp (Etype (E)))) then
            M_Arrays_1_Bool_Op.Include
              (Key      => Name,
               New_Item => Init_Array_1_Bool_Op_Module (Module));
         end if;

         if Has_Discrete_Type (Component_Type (Retysp (Etype (E)))) then
            M_Arrays_1_Comp.Include
              (Key      => Name,
               New_Item => Init_Array_1_Comp_Module (Module));
         end if;
      end if;
   end Create_Rep_Array_Theory_If_Needed;

   ----------------------
   -- Get_Array_Theory --
   ----------------------

   function Get_Array_Theory (E : Entity_Id) return M_Array_Type is
     (M_Arrays.Element (Get_Array_Theory_Name (E)));

   ------------------------
   -- Get_Array_Theory_1 --
   ------------------------

   function Get_Array_Theory_1 (E : Entity_Id) return M_Array_1_Type is
     (M_Arrays_1.Element (Get_Array_Theory_Name (E)));

   -----------------------------
   -- Get_Array_Theory_1_Comp --
   -----------------------------

   function Get_Array_Theory_1_Comp (E : Entity_Id) return M_Array_1_Comp_Type
   is
     (M_Arrays_1_Comp.Element (Get_Array_Theory_Name (E)));

   --------------------------------
   -- Get_Array_Theory_1_Bool_Op --
   --------------------------------

   function Get_Array_Theory_1_Bool_Op (E : Entity_Id)
                                        return M_Array_1_Bool_Op_Type is
     (M_Arrays_1_Bool_Op.Element (Get_Array_Theory_Name (E)));

end Why.Gen.Arrays;
