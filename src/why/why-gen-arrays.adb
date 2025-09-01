------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Common_Containers;         use Common_Containers;
with GNAT.Source_Info;
with Gnat2Why.Types;            use Gnat2Why.Types;
with GNATCOLL.Utils;            use GNATCOLL.Utils;
with Namet;                     use Namet;
with Sinput;                    use Sinput;
with SPARK_Atree;               use SPARK_Atree;
with SPARK_Definition;          use SPARK_Definition;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Util;                use SPARK_Util;
with Stand;                     use Stand;
with String_Utils;              use String_Utils;
with Uintp;                     use Uintp;
with Why.Atree.Builders;        use Why.Atree.Builders;
with Why.Gen.Decl;              use Why.Gen.Decl;
with Why.Gen.Init;              use Why.Gen.Init;
with Why.Gen.Names;             use Why.Gen.Names;
with Why.Gen.Terms;             use Why.Gen.Terms;
with Why.Images;                use Why.Images;
with Why.Inter;                 use Why.Inter;
with Why.Types;                 use Why.Types;

package body Why.Gen.Arrays is

   function Array_Convert_From_Base
     (Domain       : EW_Domain;
      Args         : W_Expr_Array;
      Ty           : Entity_Id;
      Relaxed_Init : Boolean) return W_Expr_Id;
   --  Call the proper Of_Array symbol on Args

   procedure Create_Array_Conversion_Theory_If_Needed
     (From         : Entity_Id;
      To           : Entity_Id;
      From_Wrapper : Boolean;
      To_Wrapper   : Boolean);
   --  Check if the conversion theory for converting from From to To has
   --  already been created. If not create it.
   --  @param Current_File the current file section. Conversion theories are
   --     always created in WF_Pure, but it may be necessary to save the
   --     currently opened theory if Current_File = WF_Pure.
   --  @param From the entity of source type of the conversion
   --  @param To the entity of target type of the conversion.
   --  @param From_Wrapper True to convert from a wrapper type.
   --  @param To_Wrapper True to convert to a wrapper type.

   procedure Create_Rep_Array_Theory
     (E            : Entity_Id;
      Module       : W_Module_Id;
      Symbols      : M_Array_Type;
      Relaxed_Init : Boolean);
   --  Create an Array theory
   --  @param E the entity of type array
   --  @param Module the module in which the theory should be created
   --  @param Symbols the symbols to declared in this theory
   --  @param Relaxed_Init True to declare a theory for the wrapper type

   procedure Create_Rep_Array_Theory_If_Needed
     (E : Entity_Id; Relaxed_Init : Boolean);
   --  Check if the Array theory of the representation type of E has already
   --  been created. If not create it.
   --  @param E the entity of type array
   --  @param Relaxed_Init True to create a theory for init wrappers

   procedure Declare_Ada_Array
     (Th : Theory_UC; E : Entity_Id; Relaxed_Init : Boolean);
   --  Clone the appropriate module for E. If Relaxed_Init is True, the
   --  clone is for the wrapper type.

   procedure Declare_Constrained
     (Th         : Theory_UC;
      Und_Ent    : Entity_Id;
      Base_Subst : W_Clone_Substitution_Array);
   --  Output a declaration for statically constrained array types.
   --  @param Section The section in which the declaration should be added
   --  @param Und_Ent The entity of the array type to be translated. It should
   --         be a statically constrained array type.
   --  @param Base_Subst substitution for the name of the map type and the
   --         boolean equality if any.
   --  Here we don't need a name for the type in why as no type will be
   --  declared in this module.

   procedure Declare_Unconstrained
     (Th             : Theory_UC;
      Why3_Type_Name : W_Name_Id;
      Und_Ent        : Entity_Id;
      Base_Subst     : W_Clone_Substitution_Array);
   --  Output a declaration for unconstrained and dynamically constrained array
   --  types.
   --  @param Section The section in which the declaration should be added
   --  @param Why3_Type_Name Name to be used in Why for the type
   --  @param Und_Ent The entity of the array type to be translated. It should
   --         be either an unconstrained array type or a dynamically
   --         constrained array type.
   --  @param Base_Subst substitution for the name of the map type and the
   --         boolean equality if any.

   --  The following two procedures take an array [Args] and an index [Arg_Ind]
   --  as in-out parameters. They fill the array with a number of parameters,
   --  starting from the initial value of [Arg_Ind], and set the final value
   --  of [Arg_Ind] to the index after the last written value.

   function Get_Comparison_Theory_Name (Name : Symbol) return Symbol
   is (NID (Img (Name) & To_String (WNE_Array_Comparison_Suffix)));
   --  @param Name name of an array representative theory
   --  @return The name of the theory for the comparison operators on these
   --          arrays.

   function Get_Logical_Op_Theory_Name (Name : Symbol) return Symbol
   is (NID (Img (Name) & To_String (WNE_Array_Logical_Op_Suffix)));
   --  @param Name name of an array representative theory
   --  @return The name of the theory for the logical operators on these
   --          arrays.

   function New_Length_Equality
     (L_First_E : W_Term_Id;
      L_Last_E  : W_Term_Id;
      R_First_E : W_Term_Id;
      R_Last_E  : W_Term_Id;
      Base_Ty   : W_Type_Id) return W_Pred_Id;
   --  @param L_First_E first bound of the left array
   --  @param L_Last_E last bound of the left array
   --  @param R_First_E first bound of the right array
   --  @param R_Last_E last bound of the right array
   --  @param Base_Ty type of the bound expressions
   --  @return and expression stating that left and right have the same length
   --      avoiding the wraparound semantics on bitvectors.

   function Prepare_Indexes_Substitutions
     (Th : Theory_UC; Typ : Entity_Id; Prefix : String)
      return W_Clone_Substitution_Array;
   --  @param Typ The representation type of the index
   --  @param Prefix The prefix of the current index ("I1" e.g.)
   --  @return the substitution array for cloning the indice module of
   --          _gnatprove_standard.mlw

   function Prepare_Standard_Array_Logical_Substitutions
     (Th : Theory_UC; Und_Ent : Entity_Id; Symbols : M_Array_Type)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @param Symbols the symbols for the array theory.
   --  @return An array of substitutions for cloning the module
   --          Standard_Array_Logical_Ax.

   function Prepare_Subtype_Array_Logical_Substitutions
     (Th : Theory_UC; Und_Ent : Entity_Id; Symbols : M_Array_Type)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @param Symbols the symbols for the array theory.
   --  @return An array of substitutions for cloning the module
   --          Subtype_Array_Logical_Ax.

   procedure Declare_Equality_Function
     (E : Entity_Id; Th : Theory_UC; Symbols : M_Array_Type);
   --  @param E Entity of an array type.
   --  @param Symbols the symbols for the array theory.
   --  Declare the predefined equality for E

   procedure Declare_Logical_Operation_Symbols
     (E : Entity_Id; Module : W_Module_Id; Symbols : M_Array_Type);
   --  @param E Entity of the one dimensional array type of Booleans
   --  @param File The section in which the declaration should be added
   --  @param Module The module for these declarations
   --  @param Symbols the symbols for the array theory.
   --  Clone module for logical operators (see M_Array_1_Bool_Op_Type)

   procedure Declare_Comparison_Symbols
     (E : Entity_Id; Module : W_Module_Id; Symbols : M_Array_Type);
   --  @param E Entity of the one dimensional array type of discrete values
   --  @param File The section in which the declaration should be added
   --  @param Module The module for these declarations
   --  @param Symbols the symbols for the array theory
   --  Clone module for comparison functions (see M_Array_Comp_Type)

   procedure Declare_Getter_And_Setter
     (Th       : Theory_UC;
      E        : Entity_Id;
      Arr_Ty   : W_Type_Id;
      Comp_Ty  : W_Type_Id;
      Get_Symb : W_Identifier_Id;
      Set_Symb : W_Identifier_Id);
   --  Emit definitions for get and set as for infinite maps. Set is only
   --  defined in programs, it is defined using a postcondition. Generate:
   --
   --   function get (arr : arr_ty) (i_1 : index_1) ... : comp_ty
   --   val set (arr : arr_ty) ... (comp : comp_ty) : arr_ty
   --      ensures
   --       { get result i_1 ... = comp /\
   --         (forall j_1 : index_1, .... (j_1 <> i_1 \/ ...) ->
   --             get result i_1 ... = get arr i_1 ...) }
   --
   --  This is used to create flag trees for Is_Moved and validity.

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
      if Has_Static_Array_Type (Ty) then
         Args (Arg_Ind) := Expr;
      else
         Args (Arg_Ind) :=
           New_Call
             (Domain => Domain,
              Name   => E_Symb (Ty, WNE_To_Array, Is_Init_Wrapper_Type (W_Ty)),
              Args   => (1 => Expr),
              Typ    => EW_Split (Ty, Is_Init_Wrapper_Type (W_Ty)));
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
      Arg_Ind : in out Positive) is
   begin
      Args (Arg_Ind) :=
        Insert_Conversion_To_Rep_No_Bool
          (Domain, +Get_Array_Attr (+Expr, Attr, Dim));
      Arg_Ind := Arg_Ind + 1;
   end Add_Attr_Arg;

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive;
      Params  : Transformation_Params := Body_Params) is
   begin
      Args (Arg_Ind) :=
        Insert_Conversion_To_Rep_No_Bool
          (Domain,
           +Get_Array_Attr (Term_Domain (Domain), Ty, Attr, Dim, Params));
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

   ----------------
   -- Append_Num --
   ----------------

   function Append_Num (S : String; Count : Positive) return String
   is (if Count = 1 then S else S & "_" & Image (Count, 1));

   -----------------------------
   -- Array_Convert_From_Base --
   -----------------------------

   function Array_Convert_From_Base
     (Domain       : EW_Domain;
      Args         : W_Expr_Array;
      Ty           : Entity_Id;
      Relaxed_Init : Boolean) return W_Expr_Id
   is (New_Call
         (Domain => Domain,
          Name   => E_Symb (Ty, WNE_Of_Array, Relaxed_Init),
          Args   => Args,
          Typ    => EW_Abstract (Ty, Relaxed_Init => Relaxed_Init)));

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Ar     : W_Expr_Id;
      First  : W_Expr_Id;
      Last   : W_Expr_Id) return W_Expr_Id
   is
      First_Int    : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain, Expr => First);
      Last_Int     : constant W_Expr_Id :=
        Insert_Conversion_To_Rep_No_Bool (Domain, Expr => Last);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Get_Type (Ar));

   begin
      return
        Array_Convert_From_Base
          (Domain       => Domain,
           Args         => (1 => Ar, 2 => First_Int, 3 => Last_Int),
           Ty           => Ty,
           Relaxed_Init => Relaxed_Init);
   end Array_Convert_From_Base;

   function Array_Convert_From_Base
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Ar     : W_Expr_Id;
      Bounds : W_Expr_Array) return W_Expr_Id
   is
      Relaxed_Init     : constant Boolean :=
        Is_Init_Wrapper_Type (Get_Type (Ar));
      Converted_Bounds : W_Expr_Array (Bounds'Range);
   begin
      for J in Bounds'Range loop
         Converted_Bounds (J) :=
           Insert_Conversion_To_Rep_No_Bool (Domain, Expr => Bounds (J));
      end loop;

      return
        Array_Convert_From_Base
          (Domain       => Domain,
           Args         => Ar & Converted_Bounds,
           Ty           => Ty,
           Relaxed_Init => Relaxed_Init);
   end Array_Convert_From_Base;

   function Array_Convert_From_Base
     (Domain : EW_Domain; Old_Ar : W_Expr_Id; New_Base : W_Expr_Id)
      return W_Expr_Id
   is
      Ty           : constant W_Type_Id := Get_Type (New_Base);
      Ty_Ent       : constant Entity_Id := Get_Ada_Node (+Ty);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Ty);
      Len          : constant Integer :=
        1 + 2 * Integer (Number_Dimensions (Ty_Ent));
      Args         : W_Expr_Array (1 .. Len);
      Count        : Positive := 1;
   begin
      Add_Array_Arg (Domain, Args, Old_Ar, Count);
      Args (1) := New_Base;
      return
        Array_Convert_From_Base
          (Domain       => Domain,
           Args         => Args,
           Ty           => Ty_Ent,
           Relaxed_Init => Relaxed_Init);
   end Array_Convert_From_Base;

   ---------------------------
   -- Array_Convert_To_Base --
   ---------------------------

   function Array_Convert_To_Base
     (Domain : EW_Domain; Ar : W_Expr_Id) return W_Expr_Id
   is
      Ty           : constant W_Type_Id := Get_Type (Ar);
      Ty_Ent       : constant Entity_Id := Get_Ada_Node (+Ty);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Ty);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (Ty_Ent, WNE_To_Array, Relaxed_Init),
           Args   => (1 => +Ar),
           Typ    => EW_Split (Ty_Ent, Relaxed_Init => Relaxed_Init));
   end Array_Convert_To_Base;

   ---------------------------
   -- Array_From_Split_Form --
   ---------------------------

   function Array_From_Split_Form
     (I : Item_Type; Ref_Allowed : Boolean) return W_Term_Id
   is
      Ty           : constant W_Type_Id := Get_Typ (I.Content.B_Name);
      Ty_Ent       : constant Entity_Id := Get_Ada_Node (+Ty);
      Relaxed_Init : constant Boolean := Get_Relaxed_Init (Ty);
      Len          : constant Integer :=
        2 * Integer (Number_Dimensions (Ty_Ent));
      Args         : W_Expr_Array (1 .. Len);
      Arr          : W_Expr_Id;
   begin
      if Ref_Allowed and then I.Content.Mutable then
         Arr :=
           New_Deref
             (Right => I.Content.B_Name, Typ => Get_Typ (I.Content.B_Name));
      else
         Arr := +I.Content.B_Name;
      end if;

      for Count in 1 .. Integer (Number_Dimensions (Ty_Ent)) loop
         Args (Count * 2 - 1) :=
           Insert_Conversion_To_Rep_No_Bool (EW_Term, +I.Bounds (Count).First);
         Args (Count * 2) :=
           Insert_Conversion_To_Rep_No_Bool (EW_Term, +I.Bounds (Count).Last);
      end loop;

      return
        +Array_Convert_From_Base
           (Domain       => EW_Term,
            Args         => Arr & Args,
            Ty           => Ty_Ent,
            Relaxed_Init => Relaxed_Init);
   end Array_From_Split_Form;

   -------------------------------
   -- Array_Type_Cloned_Subtype --
   -------------------------------

   function Array_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id is
      Result : Entity_Id := Retysp (E);
   begin
      while not Is_Static_Array_Type (Result)
        and then Retysp (Etype (Result)) /= Result
      loop
         Result := Retysp (Etype (Result));
      end loop;

      return Result;
   end Array_Type_Cloned_Subtype;

   -------------------------
   -- Array_Type_Is_Clone --
   -------------------------

   function Array_Type_Is_Clone (E : Entity_Id) return Boolean
   is (not Is_Static_Array_Type (Retysp (E))
       and then Retysp (Etype (E)) /= Retysp (E));

   --------------------------------------
   -- Build_Binary_Predicate_For_Array --
   --------------------------------------

   function Build_Binary_Predicate_For_Array
     (Expr1, Expr2 : W_Term_Id; Ty : Entity_Id) return W_Pred_Id
   is
      Ty_Ext     : constant Entity_Id := Retysp (Ty);
      Dim        : constant Positive := Positive (Number_Dimensions (Ty_Ext));
      Vars       : Binder_Array (1 .. Dim);
      Indexes    : W_Expr_Array (1 .. Dim);
      Range_Expr : W_Pred_Id := True_Pred;
      Index      : Node_Id := First_Index (Ty_Ext);
      I          : Positive := 1;
      T_Comp     : W_Expr_Id;
      Tmp        : W_Identifier_Id;
      Q_Expr     : W_Pred_Id;
   begin
      while Present (Index) loop
         Tmp := New_Temp_Identifier (Typ => Base_Why_Type_No_Bool (Index));
         Vars (I) :=
           Binder_Type'
             (Ada_Node => Empty,
              B_Name   => Tmp,
              B_Ent    => Null_Entity_Name,
              Mutable  => False,
              Labels   => <>);
         Indexes (I) := +Tmp;
         Range_Expr :=
           +New_And_Expr
              (Left   => +Range_Expr,
               Right  => New_Array_Range_Expr (+Tmp, +Expr1, EW_Pred, I),
               Domain => EW_Pred);
         Next_Index (Index);
         I := I + 1;
      end loop;

      pragma Assert (I = Indexes'Last + 1);

      --  Call Build_Predicate_For_Comp on the array components.

      T_Comp :=
        +Build_Predicate_For_Comp
           (C_Expr1 => +New_Array_Access (Empty, +Expr1, Indexes, EW_Term),
            C_Expr2 => +New_Array_Access (Empty, +Expr2, Indexes, EW_Term),
            C_Ty    => Component_Type (Ty_Ext),
            Idx     => Indexes);

      if T_Comp /= +True_Pred then
         T_Comp :=
           New_Conditional
             (Domain    => EW_Pred,
              Condition => +Range_Expr,
              Then_Part => T_Comp,
              Typ       => EW_Bool_Type);

         Q_Expr := New_Universal_Quantif (Binders => Vars, Pred => +T_Comp);

         return Q_Expr;
      else
         return True_Pred;
      end if;
   end Build_Binary_Predicate_For_Array;

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
   begin
      if Typ = EW_Int_Type then
         return
           New_Call
             (Domain => Domain,
              Name   => M_Integer.Length,
              Typ    => EW_Int_Type,
              Args   => (+First_Rep, +Last_Rep));
      elsif Why_Type_Is_BitVector (Typ) then
         declare
            Cond : constant W_Expr_Id :=
              New_Call
                (Domain => Domain,
                 Name   => MF_BVs (Typ).Ule,
                 Typ    => EW_Bool_Type,
                 Args   => (+First_Rep, +Last_Rep));
            Len  : constant W_Expr_Id :=
              New_Discrete_Add
                (Domain,
                 New_Discrete_Substract (Domain, Last_Rep, First_Rep),
                 New_Discrete_Constant (Value => Uint_1, Typ => Typ));
         begin
            return
              New_Conditional
                (Domain    => Domain,
                 Condition => Cond,
                 Then_Part => Len,
                 Else_Part =>
                   New_Discrete_Constant (Value => Uint_0, Typ => Typ),
                 Typ       => Typ);
         end;
      else
         raise Program_Error;
      end if;
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
           +Get_Array_Attr (+Expr, Attribute_First, Dim),
           +Get_Array_Attr (+Expr, Attribute_Last, Dim),
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
           +Get_Array_Attr (Term_Domain (Domain), Ty, Attribute_First, Dim),
           +Get_Array_Attr (Term_Domain (Domain), Ty, Attribute_Last, Dim),
           Typ);
   end Build_Length_Expr;

   -------------------------------
   -- Build_Predicate_For_Array --
   -------------------------------

   function Build_Predicate_For_Array
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id
   is
      function Build_Predicate_For_Comp
        (C_Expr1, Dummy_Expr2 : W_Term_Id;
         C_Ty                 : Entity_Id;
         Idx                  : W_Expr_Array) return W_Pred_Id
      is (Build_Predicate_For_Comp (C_Expr1, C_Ty, Idx));

      function Build_Predicate is new
        Build_Binary_Predicate_For_Array (Build_Predicate_For_Comp);

   begin
      return Build_Predicate (Expr, Expr, Ty);
   end Build_Predicate_For_Array;

   ----------------------------------------------
   -- Create_Array_Conversion_Theory_If_Needed --
   ----------------------------------------------

   procedure Create_Array_Conversion_Theory_If_Needed
     (From : Entity_Id; To : Entity_Id; Relaxed_Init : Boolean := False) is
   begin
      Create_Array_Conversion_Theory_If_Needed
        (From         => From,
         To           => To,
         From_Wrapper => Relaxed_Init,
         To_Wrapper   => Relaxed_Init);
   end Create_Array_Conversion_Theory_If_Needed;

   procedure Create_Array_Conversion_Theory_If_Needed
     (From         : Entity_Id;
      To           : Entity_Id;
      From_Wrapper : Boolean;
      To_Wrapper   : Boolean)
   is
      use Name_Id_Name_Id_Conversion_Name_Map;

      From_Name  : constant Symbol :=
        Get_Array_Theory_Name (From, From_Wrapper);
      To_Name    : constant Symbol := Get_Array_Theory_Name (To, To_Wrapper);
      From_Symb  : constant M_Array_Type := M_Arrays.Element (From_Name);
      To_Symb    : constant M_Array_Type := M_Arrays.Element (To_Name);
      Module     : constant W_Module_Id :=
        New_Module
          (File => No_Symbol,
           Name => Img (From_Name) & "__to__" & Img (To_Name));
      Convert_Id : constant W_Identifier_Id :=
        New_Identifier
          (Name => "convert", Module => Module, Typ => To_Symb.Ty);
      A_Binder   : constant Binder_Type :=
        (Ada_Node => Standard.Types.Empty,
         B_Name   => New_Identifier (Name => "a", Typ => From_Symb.Ty),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Labels   => <>);
      B_Binder   : constant Binder_Type :=
        (Ada_Node => Standard.Types.Empty,
         B_Name   => New_Identifier (Name => "b", Typ => To_Symb.Ty),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Labels   => <>);

      C         : Name_Id_Name_Id_Conversion_Name_Map.Cursor;
      Not_Found : Boolean;

      Th : Theory_UC;
   begin
      --  Search for From_Name in M_Arrays_Conversion and initialize its value
      --  to Empty_Map if it is not found.

      M_Arrays_Conversion.Insert
        (Key => From_Name, Position => C, Inserted => Not_Found);

      --  If there is a mapping for From_Name in M_Arrays_Conversion and it
      --  contains To_Name, then there is nothing to do.

      if not Not_Found and then M_Arrays_Conversion (C).Contains (To_Name) then
         return;
      end if;

      Th :=
        Open_Theory
          (WF_Context,
           Module,
           Comment =>
             "Module for array conversion from type "
             & """"
             & Get_Name_String (Chars (From))
             & """"
             & (if Sloc (From) > 0
                then " defined at " & Build_Location_String (Sloc (From))
                else "")
             & " to type "
             & """"
             & Get_Name_String (Chars (To))
             & """"
             & (if Sloc (To) > 0
                then " defined at " & Build_Location_String (Sloc (To))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an abstract conversion function from From to To

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (Convert_Id),
            Binders     => (1 => A_Binder),
            Location    => No_Location,
            Return_Type => To_Symb.Ty,
            Labels      => Symbol_Sets.Empty_Set));

      --  Generate an axiom for the conversion function:
      --  axiom convert__def:
      --    forall a : <from>.
      --      let b = convert a in
      --        forall i1 : <from.index_type1>, i2 : ....
      --          to_base (get a i1 i2 ...) = to_base (get b i1 i2 ...)

      declare
         Call_Expr : constant W_Term_Id :=
           +New_Call
              (Name    => To_Local (Convert_Id),
               Domain  => EW_Term,
               Binders => (1 => A_Binder),
               Typ     => To_Symb.Ty);
         Ty_Ext    : constant Entity_Id := Retysp (From);
         Dim       : constant Positive :=
           Positive (Number_Dimensions (Ty_Ext));
         Indexes   : Binder_Array (1 .. Dim);
         Index     : Node_Id := First_Index (Ty_Ext);
         I         : Positive := 1;
         T_Comp    : W_Pred_Id := True_Pred;
         Tmp       : W_Identifier_Id;
         T         : W_Pred_Id := True_Pred;

      begin
         while Present (Index) loop
            Tmp := New_Temp_Identifier (Typ => Base_Why_Type_No_Bool (Index));
            Indexes (I) :=
              Binder_Type'
                (Ada_Node => Standard.Types.Empty,
                 B_Name   => Tmp,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);
            Next_Index (Index);
            I := I + 1;
         end loop;

         pragma Assert (I = Indexes'Last + 1);

         --  Generate equality of array components

         declare
            From_Comp    : constant Entity_Id :=
              Retysp (Component_Type (From));
            To_Comp      : constant Entity_Id := Retysp (Component_Type (To));
            Relaxed_Init : constant Boolean :=
              (To_Wrapper or else Has_Relaxed_Init (To_Comp));
            --  We use partially initialized expressions if the target is
            --  partially initialized. If the source only is partially
            --  initialized, we ignore the init flags lest we might generate
            --  an unsound axiom. Initialization checks will be inserted
            --  independently.

            A_Comp : W_Term_Id :=
              New_Call
                (Name    => From_Symb.Get,
                 Binders => A_Binder & Indexes,
                 Typ     =>
                   EW_Abstract
                     (From_Comp,
                      Relaxed_Init =>
                        Has_Relaxed_Init (From_Comp) or else From_Wrapper));
            B_Comp : W_Term_Id :=
              New_Call
                (Name    => To_Symb.Get,
                 Binders => B_Binder & Indexes,
                 Typ     =>
                   EW_Abstract
                     (To_Comp,
                      Relaxed_Init =>
                        Has_Relaxed_Init (To_Comp) or else To_Wrapper));

         begin
            --  Possibly convert the first operand

            if (Has_Relaxed_Init (From_Comp) or else From_Wrapper)
              /= Relaxed_Init
            then
               A_Comp :=
                 Insert_Simple_Conversion
                   (Expr => A_Comp,
                    To   =>
                      EW_Abstract (From_Comp, Relaxed_Init => Relaxed_Init));
            end if;

            --  If we are converting scalars, the equality will be stated on
            --  the base type which does not include an init flag. If the
            --  conversion should be done on wrappers, assume preservation of
            --  the init flag separately.

            if Relaxed_Init and then Is_Scalar_Type (From_Comp) then
               T_Comp :=
                 New_Comparison
                   (Symbol => Why_Eq,
                    Left   =>
                      New_Init_Attribute_Access
                        (E => From_Comp, Name => +A_Comp),
                    Right  =>
                      New_Init_Attribute_Access
                        (E => To_Comp, Name => +B_Comp));
            end if;

            --  Do the actual conversion.
            --  If components are arrays, go to split form.

            if Is_Array_Type (From_Comp) then
               if not Has_Static_Array_Type (From_Comp) then
                  A_Comp := +Array_Convert_To_Base (EW_Term, +A_Comp);
               end if;

               if not Has_Static_Array_Type (To_Comp) then
                  B_Comp := +Array_Convert_To_Base (EW_Term, +B_Comp);
               end if;

            --  Otherwise, use base type

            else
               declare
                  BT      : constant W_Type_Id := Base_Why_Type (From_Comp);
                  Init_BT : constant W_Type_Id :=
                    (if not Relaxed_Init or else Is_Scalar_Type (From_Comp)
                     then BT
                     else EW_Init_Wrapper (BT));
               begin
                  A_Comp :=
                    Insert_Simple_Conversion (Expr => A_Comp, To => Init_BT);
                  B_Comp :=
                    Insert_Simple_Conversion (Expr => B_Comp, To => Init_BT);
               end;
            end if;

            T_Comp :=
              New_And_Pred
                (Left  => T_Comp,
                 Right =>
                   New_Comparison
                     (Symbol => Why_Eq, Left => A_Comp, Right => B_Comp));
         end;

         T := New_Universal_Quantif (Binders => Indexes, Pred => T_Comp);

         T :=
           +New_Typed_Binding
              (Domain  => EW_Pred,
               Name    => B_Binder.B_Name,
               Def     => +Call_Expr,
               Context => +T);

         Emit
           (Th,
            New_Guarded_Axiom
              (Name    => NID ("convert__def"),
               Binders => (1 => A_Binder),
               Def     => T,
               Dep     =>
                 New_Axiom_Dep
                   (Name => To_Local (Convert_Id), Kind => EW_Axdep_Func)));
      end;

      Close_Theory (Th, Kind => Definition_Theory);

      M_Arrays_Conversion (C).Insert (To_Name, Convert_Id);
   end Create_Array_Conversion_Theory_If_Needed;

   ---------------------------------------
   -- Create_Move_Tree_Theory_For_Array --
   ---------------------------------------

   procedure Create_Move_Tree_Theory_For_Array (Th : Theory_UC; E : Entity_Id)
   is
      Ty_Name    : constant W_Name_Id := To_Name (WNE_Move_Tree);
      Tree_Ident : constant W_Identifier_Id :=
        New_Identifier
          (Name => "tree", Typ => New_Named_Type (Name => Ty_Name));
      Comp_Tree  : constant W_Type_Id :=
        Get_Move_Tree_Type (Component_Type (E));

   begin
      Emit (Th, New_Type_Decl (To_String (WNE_Move_Tree)));

      Emit_Ref_Type_Definition (Th => Th, Name => Ty_Name);

      Declare_Getter_And_Setter
        (Th       => Th,
         E        => E,
         Arr_Ty   => New_Named_Type (Name => Ty_Name),
         Comp_Ty  => Comp_Tree,
         Get_Symb => To_Local (E_Symb (E, WNE_Move_Tree_Array_Get)),
         Set_Symb => To_Local (E_Symb (E, WNE_Move_Tree_Array_Set)));

      --  Create __is_moved_or_reclaimed predicate. Generate:
      --
      --    predicate __is_moved_or_reclaimed (tree : move_tree) (obj : ty) =
      --      (forall i_1 : index_1, ....
      --          obj.first <= i_1 <= obj.last /\ ... ->
      --          __is_moved_or_reclaimed (get tree i_1 ...) (get obj i_1 ...))

      declare
         Typ       : constant W_Type_Id :=
           (if Has_Init_Wrapper (E)
            then EW_Init_Wrapper (Type_Of_Node (E))
            else Type_Of_Node (E));
         Obj_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "obj", Typ => Typ);

         function Is_Moved_For_Comp
           (C_Expr : W_Term_Id; C_Ty : Entity_Id; Idx : W_Expr_Array)
            return W_Pred_Id;

         ----------------------
         -- Is_Moved_For_Comp --
         ----------------------

         function Is_Moved_For_Comp
           (C_Expr : W_Term_Id; C_Ty : Entity_Id; Idx : W_Expr_Array)
            return W_Pred_Id is
         begin
            return
              New_Call
                (Name => E_Symb (C_Ty, WNE_Is_Moved_Or_Reclaimed),
                 Args =>
                   (1 =>
                      New_Call
                        (Name   =>
                           To_Local (E_Symb (E, WNE_Move_Tree_Array_Get)),
                         Args   => +Tree_Ident & Idx,
                         Domain => EW_Term),
                    2 => +C_Expr));
         end Is_Moved_For_Comp;

         function Is_Moved_For_Array is new
           Build_Predicate_For_Array (Is_Moved_For_Comp);

         Def : constant W_Pred_Id := Is_Moved_For_Array (+Obj_Ident, E);

      begin
         Emit
           (Th,
            New_Function_Decl
              (Domain   => EW_Pred,
               Name     => To_Local (E_Symb (E, WNE_Is_Moved_Or_Reclaimed)),
               Binders  =>
                 Binder_Array'
                   (1 => (B_Name => Tree_Ident, others => <>),
                    2 => (B_Name => Obj_Ident, others => <>)),
               Location => No_Location,
               Labels   => Symbol_Sets.Empty_Set,
               Def      => +Def));
      end;
   end Create_Move_Tree_Theory_For_Array;

   -----------------------------
   -- Create_Rep_Array_Theory --
   -----------------------------

   procedure Create_Rep_Array_Theory
     (E            : Entity_Id;
      Module       : W_Module_Id;
      Symbols      : M_Array_Type;
      Relaxed_Init : Boolean)
   is
      Typ : constant Entity_Id := Retysp (Etype (E));

      Dim : constant Positive := Positive (Number_Dimensions (Typ));

      Subst : W_Clone_Substitution_Array (1 .. Dim * 7 + 1);
      --  ??? why 7

      Th : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module,
           Comment =>
             "Module for axiomatizing the array theory associated to type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  Start by generating all the substitutions for the theory(ies)
      --  Array__Index

      declare
         Index : Node_Id := First_Index (Typ);
      begin
         for I in 0 .. Dim - 1 loop

            Subst (I * 7 + 1 .. I * 7 + 7) :=
              Prepare_Indexes_Substitutions
                (Th, Retysp (Etype (Index)), "I" & Image (I + 1, 1));

            Next_Index (Index);

         end loop;
      end;

      --  Add the substitution for the component type

      Subst (Subst'Last) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => To_Name (WNE_Array_Component_Type),
           Image     => To_Name (WNE_Array_Component_Type));

      --  Declare the component type and clone the appropriate array theory.

      Emit
        (Th,
         New_Type_Decl
           (Name  => To_Name (WNE_Array_Component_Type),
            Alias =>
              EW_Abstract
                (Component_Type (Typ),
                 Relaxed_Init =>
                   Has_Relaxed_Init (Component_Type (Typ))
                   or else Relaxed_Init)));

      Emit
        (Th,
         New_Clone_Declaration
           (Theory_Kind   => EW_Theory,
            Clone_Kind    => EW_Export,
            Origin        => Array_Modules (Dim),
            As_Name       => No_Symbol,
            Substitutions => Subst));

      --  Equality should never be called on partially initialized objects

      if not Relaxed_Init then
         Declare_Equality_Function (Typ, Th, Symbols);
      end if;

      Close_Theory (Th, Kind => Definition_Theory);
   end Create_Rep_Array_Theory;

   ---------------------------------------
   -- Create_Rep_Array_Theory_If_Needed --
   ---------------------------------------

   procedure Create_Rep_Array_Theory_If_Needed
     (E : Entity_Id; Relaxed_Init : Boolean)
   is
      Name    : constant Symbol := Get_Array_Theory_Name (E, Relaxed_Init);
      Module  : constant W_Module_Id :=
        New_Module (File => No_Symbol, Name => Img (Name));
      Symbols : constant M_Array_Type := Init_Array_Module (Module);

   begin
      if M_Arrays.Contains (Key => Name) then
         return;
      end if;

      --  If Name was inserted it means that the theory is not present:
      --  let's create it.

      Create_Rep_Array_Theory (E, Module, Symbols, Relaxed_Init);

      M_Arrays.Include (Key => Name, New_Item => Symbols);

      --  For arrays of dimension 1, we may need to clone additional modules
      --  containing definition for the comparison function (if the component
      --  type is discrete) or of boolean operators (if the component type is
      --  boolean).

      if Number_Dimensions (Retysp (Etype (E))) = 1 then
         M_Arrays_1.Include
           (Key => Name, New_Item => Init_Array_1_Module (Module));

         --  For arrays of boolean types of dimension 1 we need to define the
         --  logical operators.

         if not Relaxed_Init
           and then Has_Boolean_Type (Component_Type (Retysp (Etype (E))))
         then
            declare
               Bool_Op_Module : constant W_Module_Id :=
                 New_Module
                   (File => No_Symbol,
                    Name => Img (Get_Logical_Op_Theory_Name (Name)));
            begin
               Declare_Logical_Operation_Symbols (E, Bool_Op_Module, Symbols);
               M_Arrays_1_Bool_Op.Include
                 (Key      => Name,
                  New_Item => Init_Array_1_Bool_Op_Module (Bool_Op_Module));
            end;
         end if;

         --  For arrays of discrete types of dimension 1 we need to define the
         --  comparison operators.

         if not Relaxed_Init
           and then Has_Discrete_Type (Component_Type (Retysp (Etype (E))))
         then
            declare
               Comp_Module : constant W_Module_Id :=
                 New_Module
                   (File => No_Symbol,
                    Name => Img (Get_Comparison_Theory_Name (Name)));
            begin
               Declare_Comparison_Symbols (E, Comp_Module, Symbols);
               M_Arrays_1_Comp.Include
                 (Key      => Name,
                  New_Item => Init_Array_1_Comp_Module (Comp_Module));
            end;
         end if;
      end if;
   end Create_Rep_Array_Theory_If_Needed;

   procedure Create_Rep_Array_Theory_If_Needed (E : Entity_Id) is
   begin
      Create_Rep_Array_Theory_If_Needed (E => E, Relaxed_Init => False);

      --  Also create a theory for the wrapper type if we need one

      if Has_Init_Wrapper (E) then
         Create_Rep_Array_Theory_If_Needed (E => E, Relaxed_Init => True);

         --  Create conversion functions to and from the wrapper type

         Create_Array_Conversion_Theory_If_Needed
           (From => E, To => E, From_Wrapper => True, To_Wrapper => False);

         Create_Array_Conversion_Theory_If_Needed
           (From => E, To => E, From_Wrapper => False, To_Wrapper => True);
      end if;
   end Create_Rep_Array_Theory_If_Needed;

   -------------------------------------------
   -- Create_Validity_Tree_Theory_For_Array --
   -------------------------------------------

   procedure Create_Validity_Tree_Theory_For_Array
     (Th : Theory_UC; E : Entity_Id)
   is
      Ty_Name     : constant W_Name_Id := To_Name (WNE_Validity_Tree);
      Tree_Ty     : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
      Comp_Ty     : constant Type_Kind_Id := Component_Type (E);
      Comp_Tree   : constant W_Type_Id := Get_Validity_Tree_Type (Comp_Ty);
      Tree_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "tree", Typ => Tree_Ty);
      Tree_Binder : constant Binder_Type :=
        Binder_Type'
          (Ada_Node => Empty,
           B_Name   => Tree_Ident,
           B_Ent    => Null_Entity_Name,
           Mutable  => False,
           Labels   => <>);
      Dim         : constant Positive := Positive (Number_Dimensions (E));
      Get_Name    : constant W_Identifier_Id :=
        To_Local (E_Symb (E, WNE_Validity_Tree_Get));

   begin
      Emit
        (Th, New_Type_Decl (Name => Ty_Name, Labels => Symbol_Sets.Empty_Set));

      Emit_Ref_Type_Definition (Th => Th, Name => Ty_Name);
      Emit (Th, New_Havoc_Declaration (Name => Ty_Name));

      Declare_Getter_And_Setter
        (Th       => Th,
         E        => E,
         Arr_Ty   => Tree_Ty,
         Comp_Ty  => Comp_Tree,
         Get_Symb => Get_Name,
         Set_Symb => To_Local (E_Symb (E, WNE_Validity_Tree_Set)));

      --  Generate a function for sliding. Generate:
      --
      --
      --  let function __slide
      --       (tree : Ty_Name) (old_f1, new_f1 : I1.t) ... : Ty_Name
      --  axiom __slide__def:
      --    forall tree : Ty_Name, old_f1, new_f1 : I1.t ...
      --          [__slide tree old_f1 new_f1 ...].
      --     let result = __slide tree old_f1 new_f1 ... in
      --       (old_f1 = new_f1 /\ ... -> result = tree)
      --       /\ forall i1. ... get result i1 ... = get tree
      --             (i1 - new_f1 + old_f1) ...
      --       /\ forall i1. ... get tree i1 ... = get result
      --             (i1 - old_f1 + new_f1) ...

      declare
         Slide_Name  : constant W_Identifier_Id :=
           To_Local (E_Symb (E, WNE_Validity_Tree_Slide));
         Firsts      : Binder_Array (1 .. Dim * 2);
         Vars        : Binder_Array (1 .. Dim);
         Vars_To_Old : W_Expr_Array (1 .. Dim); --  (i1 - new_f1 + old_f1) ...
         Vars_To_New : W_Expr_Array (1 .. Dim); --  (i1 - old_f1 + new_f1) ...
         Eq_First    : W_Pred_Array (1 .. Dim);
         Index       : Node_Id := First_Index (E);

      begin
         for I in 1 .. Dim loop
            declare
               Idx_Ty    : constant W_Type_Id := Base_Why_Type_No_Bool (Index);
               Idx       : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "idx", Typ => Idx_Ty);
               Old_First : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "old_first", Typ => Idx_Ty);
               New_First : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "new_first", Typ => Idx_Ty);
            begin
               Vars (I) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => Idx,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Firsts (I * 2 - 1) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => Old_First,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Firsts (I * 2) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => New_First,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Eq_First (I) :=
                 New_Comparison
                   (Symbol => Why_Eq, Left => +Old_First, Right => +New_First);
               Vars_To_Old (I) :=
                 +New_Discrete_Add
                    (Domain => EW_Term,
                     Left   =>
                       New_Discrete_Substract
                         (Domain => EW_Term,
                          Left   => +Idx,
                          Right  => +New_First,
                          Typ    => Idx_Ty),
                     Right  => +Old_First,
                     Typ    => Idx_Ty);
               Vars_To_New (I) :=
                 +New_Discrete_Add
                    (Domain => EW_Term,
                     Left   =>
                       New_Discrete_Substract
                         (Domain => EW_Term,
                          Left   => +Idx,
                          Right  => +Old_First,
                          Typ    => Idx_Ty),
                     Right  => +New_First,
                     Typ    => Idx_Ty);
            end;
            Next_Index (Index);
         end loop;

         pragma Assert (No (Index));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Validity_Tree_Slide)),
               Return_Type => Tree_Ty,
               Binders     => Tree_Binder & Firsts,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set));

         declare
            Axiom_Name : constant String := "__slide__" & Def_Axiom;
            Call       : constant W_Term_Id :=
              New_Call
                (Name    => Slide_Name,
                 Binders => Tree_Binder & Firsts,
                 Typ     => Tree_Ty);
         begin
            Emit
              (Th,
               New_Guarded_Axiom
                 (Name     => NID (Axiom_Name),
                  Binders  => Tree_Binder & Firsts,
                  Triggers =>
                    New_Triggers
                      (Triggers => (1 => New_Trigger (Terms => (1 => +Call)))),
                  Def      =>
                    New_Typed_Binding
                      (Name    => New_Result_Ident (Tree_Ty),
                       Def     => Call,
                       Context =>
                         New_And_Pred
                           ((1 =>
                               New_Conditional
                                 (Condition => New_And_Pred (Eq_First),
                                  Then_Part =>
                                    New_Comparison
                                      (Symbol => Why_Eq,
                                       Left   => +New_Result_Ident (Tree_Ty),
                                       Right  => +Tree_Ident)),
                             2 =>
                               New_Universal_Quantif
                                 (Binders => Vars,
                                  Pred    =>
                                    New_Comparison
                                      (Symbol => Why_Eq,
                                       Left   =>
                                         New_Call
                                           (Name    => Get_Name,
                                            Binders =>
                                              Binder_Type'
                                                (Ada_Node => Empty,
                                                 B_Name   =>
                                                   New_Result_Ident (Tree_Ty),
                                                 B_Ent    => Null_Entity_Name,
                                                 Mutable  => False,
                                                 Labels   => <>)
                                              & Vars,
                                            Typ     => Comp_Tree),
                                       Right  =>
                                         New_Call
                                           (Name => Get_Name,
                                            Args => +Tree_Ident & Vars_To_Old,
                                            Typ  => Comp_Tree))),
                             3 =>
                               New_Universal_Quantif
                                 (Binders => Vars,
                                  Pred    =>
                                    New_Comparison
                                      (Symbol => Why_Eq,
                                       Left   =>
                                         New_Call
                                           (Name    => Get_Name,
                                            Binders => Tree_Binder & Vars,
                                            Typ     => Comp_Tree),
                                       Right  =>
                                         New_Call
                                           (Name => Get_Name,
                                            Args =>
                                              +New_Result_Ident (Tree_Ty)
                                              & Vars_To_New,
                                            Typ  => Comp_Tree)))))),
                  Dep      =>
                    New_Axiom_Dep
                      (Name => Slide_Name, Kind => EW_Axdep_Func)));
         end;
      end;

      --  Generate a is_valid function and a valid_value constant that has all
      --  its fields to True.
      --
      --  Generate:
      --
      --  predicate is_valid (tree : Ty_Name) (f1, l1 : I1.t) ... =
      --    (forall i1. f1 <= i1 <= l1 ->
      --     ...
      --       Comp.is_valid (get tree i1 ...))
      --
      --  let function valid_value : Ty_Name
      --  axiom valid_value__def
      --     forall i1. ... get valid_value i1 ... = Comp.valid_value

      declare
         Bounds : Binder_Array (1 .. Dim * 2);
         Vars   : Binder_Array (1 .. Dim);
         Ranges : W_Pred_Array (1 .. Dim);
         Index  : Node_Id := First_Index (E);

      begin
         for I in 1 .. Dim loop
            declare
               Idx_Ty   : constant W_Type_Id := Base_Why_Type_No_Bool (Index);
               Idx      : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "idx", Typ => Idx_Ty);
               First_Id : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "first", Typ => Idx_Ty);
               Last_Id  : constant W_Identifier_Id :=
                 New_Temp_Identifier (Base_Name => "last", Typ => Idx_Ty);
            begin
               Vars (I) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => Idx,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Bounds (I * 2 - 1) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => First_Id,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Bounds (I * 2) :=
                 Binder_Type'
                   (Ada_Node => Empty,
                    B_Name   => Last_Id,
                    B_Ent    => Null_Entity_Name,
                    Mutable  => False,
                    Labels   => <>);
               Ranges (I) :=
                 +New_Range_Expr
                    (Low    => +First_Id,
                     High   => +Last_Id,
                     Expr   => +Idx,
                     Domain => EW_Pred);
               Next_Index (Index);
            end;
         end loop;

         pragma Assert (No (Index));

         --  Define Is_Valid

         declare
            Get_Call     : constant W_Term_Id :=
              New_Call
                (Name    => Get_Name,
                 Binders => Tree_Binder & Vars,
                 Typ     => Comp_Tree);
            Is_Valid_Def : constant W_Pred_Id :=
              New_Universal_Quantif
                (Binders => Vars,
                 Pred    =>
                   New_Conditional
                     (Condition => New_And_Pred (Ranges),
                      Then_Part =>
                        (if Has_Scalar_Type (Comp_Ty)
                         then Pred_Of_Boolean_Term (+Get_Call)
                         else
                           +New_Is_Valid_Call_For_Constrained_Ty
                              (+Get_Call, Comp_Ty, EW_Pred, Logic_Params))));
         begin
            Emit
              (Th,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => To_Local (E_Symb (E, WNE_Is_Valid)),
                  Binders  => Tree_Binder & Bounds,
                  Location => No_Location,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => +Is_Valid_Def));
         end;

         --  Define Valid_Value

         declare
            Valid_Value_Name : constant W_Identifier_Id :=
              To_Local (E_Symb (E, WNE_Valid_Value));
            Axiom_Name       : constant String :=
              "__valid_value__" & Def_Axiom;
         begin
            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Valid_Value_Name,
                  Return_Type => Tree_Ty,
                  Binders     => Binder_Array'(1 .. 0 => <>),
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));

            Emit
              (Th,
               New_Guarded_Axiom
                 (Name    => NID (Axiom_Name),
                  Binders => (1 .. 0 => <>),
                  Def     =>
                    New_Universal_Quantif
                      (Binders => Vars,
                       Pred    =>
                         New_Comparison
                           (Symbol => Why_Eq,
                            Left   =>
                              New_Call
                                (Name    => Get_Name,
                                 Binders =>
                                   Binder_Type'
                                     (Ada_Node => Empty,
                                      B_Name   => Valid_Value_Name,
                                      B_Ent    => Null_Entity_Name,
                                      Mutable  => False,
                                      Labels   => <>)
                                   & Vars,
                                 Typ     => Comp_Tree),
                            Right  =>
                              (if Has_Scalar_Type (Comp_Ty)
                               then True_Term
                               else +E_Symb (Comp_Ty, WNE_Valid_Value)))),
                  Dep     =>
                    New_Axiom_Dep
                      (Name => Valid_Value_Name, Kind => EW_Axdep_Func)));
         end;
      end;
   end Create_Validity_Tree_Theory_For_Array;

   -----------------------
   -- Declare_Ada_Array --
   -----------------------

   procedure Declare_Ada_Array (Th : Theory_UC; E : Entity_Id) is
   begin
      Declare_Ada_Array (Th => Th, E => E, Relaxed_Init => False);
   end Declare_Ada_Array;

   procedure Declare_Ada_Array
     (Th : Theory_UC; E : Entity_Id; Relaxed_Init : Boolean)
   is
      Why_Name : constant W_Name_Id :=
        To_Why_Type (E, Local => True, Relaxed_Init => Relaxed_Init);
   begin
      if Array_Type_Is_Clone (E) then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and then return.

         declare
            Clone_Entity : constant Entity_Id := Array_Type_Cloned_Subtype (E);
            Clone_Name   : constant W_Name_Id :=
              To_Why_Type
                (Clone_Entity, Local => True, Relaxed_Init => Relaxed_Init);
            Clone_Module : constant W_Module_Id :=
              E_Module
                (Clone_Entity,
                 (if Relaxed_Init then Init_Wrapper else Regular));
         begin
            Add_With_Clause (Th, Clone_Module, EW_Export);

            --  If the copy has the same name as the original, do not redefine
            --  the type name.

            if Get_Symb (Why_Name) /= Get_Symb (Clone_Name) then
               Emit
                 (Th,
                  New_Type_Decl
                    (Name  => Why_Name,
                     Alias => +New_Named_Type (Name => Clone_Name)));
            end if;
         end;
      else
         declare
            Array_Theory : constant W_Module_Id :=
              Get_Array_Theory (E, Relaxed_Init).Module;
            Nb_Subst     : constant Positive :=
              (if Relaxed_Init then 3 else 4);
            Subst        : W_Clone_Substitution_Array (1 .. Nb_Subst);
         begin
            Emit
              (Th,
               New_Type_Decl
                 (Name  => To_Name (WNE_Array_Component_Type),
                  Alias => EW_Abstract (Component_Type (E))));

            Subst (1) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name (Symb => NID ("map")),
                 Image     =>
                   New_Name (Symb => NID ("map"), Module => Array_Theory));

            Subst (2) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symb => NID ("has_bounds")),
                 Image     =>
                   New_Name
                     (Symb => NID ("has_bounds"), Module => Array_Theory));

            Subst (3) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symb => NID ("eq_ext")),
                 Image     =>
                   New_Name (Symb => NID ("eq_ext"), Module => Array_Theory));

            --  We do not have an equality on wrapper types

            if not Relaxed_Init then
               Subst (4) :=
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name (Symb => NID ("array_bool_eq")),
                    Image     =>
                      New_Name
                        (Symb => NID ("bool_eq"), Module => Array_Theory));
            end if;

            if Is_Static_Array_Type (E) then
               Declare_Constrained (Th, E, Subst);
            else
               Declare_Unconstrained (Th, Why_Name, E, Subst);
            end if;
         end;
      end if;
   end Declare_Ada_Array;

   -------------------------------------------
   -- Declare_Additional_Symbols_For_String --
   -------------------------------------------

   procedure Declare_Additional_Symbols_For_String (Th : Theory_UC) is
      Dummy_Ident       : constant W_Identifier_Id :=
        New_Identifier (Name => "x", Typ => M_Main.String_Image_Type);
      Size_Ident        : constant W_Identifier_Id :=
        New_Identifier (Name => "s", Typ => EW_Int_Type);
      To_String_Binders : constant Binder_Array :=
        (1 =>
           Binder_Type'
             (Ada_Node => Empty,
              Mutable  => False,
              B_Ent    => Null_Entity_Name,
              B_Name   => Dummy_Ident,
              Labels   => <>),
         2 =>
           Binder_Type'
             (Ada_Node => Empty,
              Mutable  => False,
              B_Ent    => Null_Entity_Name,
              B_Name   => Size_Ident,
              Labels   => <>));
      Str_Typ           : constant W_Type_Id := EW_Abstract (Standard_String);
      Dummy_Ident2      : constant W_Identifier_Id :=
        New_Identifier (Name => "x", Typ => Str_Typ);

   begin
      Add_With_Clause (Th, Int_Module, EW_Clone_Default);
      Add_With_Clause (Th, E_Module (Standard_String), EW_Clone_Default);

      --  Declare To_String and Of_String to convert between _image and string

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (To_String_Id),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Binders     => To_String_Binders,
            Return_Type => Str_Typ));
      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (Of_String_Id),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Binders     =>
              (1 =>
                 Binder_Type'
                   (Ada_Node => Empty,
                    Mutable  => False,
                    B_Ent    => Null_Entity_Name,
                    B_Name   => Dummy_Ident2,
                    Labels   => <>)),
            Return_Type => M_Main.String_Image_Type));

      --  Add axioms for:
      --    to_string (x, s)'first = 1
      --    to_string (x, s)'length <= s
      --
      --   axiom to_string__first :
      --    (forall x   : Main.__image.
      --    (forall s   : int [to_string x s].
      --       Standard__string.first (to_string x s) = 1))
      --
      --   axiom to_string__length :
      --    (forall x   : Main.__image.
      --    (forall s   : int [to_string x s].
      --      s >= 0 -> Standard__string.length (to_string x s) <= s))

      declare
         Call_Expr : constant W_Term_Id :=
           New_Call
             (Name => To_Local (To_String_Id),
              Args => (1 => +Dummy_Ident, 2 => +Size_Ident),
              Typ  => Str_Typ);
         Guard     : constant W_Pred_Id :=
           +New_Comparison
              (Symbol => Int_Infix_Ge,
               Left   => +Size_Ident,
               Right  => New_Integer_Constant (Value => Uint_0),
               Domain => EW_Pred);
         Dep       : constant W_Axiom_Dep_Id :=
           New_Axiom_Dep
             (Name => To_Local (To_String_Id), Kind => EW_Axdep_Func);
      begin
         Emit
           (Th,
            New_Guarded_Axiom
              (Name     => NID ("to_string__first"),
               Binders  => To_String_Binders,
               Triggers =>
                 New_Triggers
                   (Triggers =>
                      (1 => New_Trigger (Terms => (1 => +Call_Expr)))),
               Def      =>
                 New_Comparison
                   (Symbol => Why_Eq,
                    Left   =>
                      Get_Array_Attr
                        (Expr => Call_Expr, Attr => Attribute_First, Dim => 1),
                    Right  =>
                      New_Discrete_Constant
                        (Value => Uint_1, Typ => EW_Int_Type)),
               Dep      => Dep));
         Emit
           (Th,
            New_Guarded_Axiom
              (Name     => NID ("to_string__length"),
               Binders  => To_String_Binders,
               Triggers =>
                 New_Triggers
                   (Triggers =>
                      (1 => New_Trigger (Terms => (1 => +Call_Expr)))),
               Pre      => Guard,
               Def      =>
                 New_Comparison
                   (Symbol => Int_Infix_Le,
                    Left   =>
                      Get_Array_Attr
                        (Expr => Call_Expr,
                         Attr => Attribute_Length,
                         Dim  => 1),
                    Right  => +Size_Ident),
               Dep      => Dep));
         Emit
           (Th,
            New_Guarded_Axiom
              (Name     => NID ("to_string__wf"),
               Binders  => To_String_Binders,
               Triggers =>
                 New_Triggers
                   (Triggers =>
                      (1 => New_Trigger (Terms => (1 => +Call_Expr)))),
               Def      => New_Well_Formed_Pred (Arr => Call_Expr),
               Dep      => Dep));
      end;
   end Declare_Additional_Symbols_For_String;

   --------------------------------
   -- Declare_Comparison_Symbols --
   --------------------------------

   procedure Declare_Comparison_Symbols
     (E : Entity_Id; Module : W_Module_Id; Symbols : M_Array_Type)
   is
      Fst_Idx       : constant Node_Id :=
        First_Index
          (if Ekind (E) = E_String_Literal_Subtype
           then Retysp (Etype (E))
           else E);
      Component_Typ : constant Entity_Id := Component_Type (E);
      Base          : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Component_Typ);
      To_Rep_Name   : W_Identifier_Id :=
        Conversion_Name (From => EW_Abstract (Component_Typ), To => Base);
      Th            : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module,
           Comment =>
             "Module for axiomatizing comparison for the array theory"
             & " associated to type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If components have wrappers, we cannot use To_Rep symbol as is.
      --  Generate a new To_Rep symbol for this case.

      if Has_Relaxed_Init (Component_Typ) then
         declare
            A_Ident  : constant W_Identifier_Id :=
              New_Identifier
                (Name => "a",
                 Typ  => EW_Abstract (Component_Typ, Relaxed_Init => True));
            A_Binder : constant Binder_Array :=
              (1 => (B_Name => A_Ident, others => <>));
         begin
            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (To_Rep_Name),
                  Binders     => A_Binder,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => Base,
                  Def         =>
                    New_Call
                      (Domain => EW_Term,
                       Name   => To_Rep_Name,
                       Args   =>
                         (1 =>
                            Insert_Simple_Conversion
                              (Ada_Node => Empty,
                               Domain   => EW_Term,
                               Expr     => +A_Ident,
                               To       => EW_Abstract (Component_Typ))),
                       Typ    => Base)));

            To_Rep_Name := To_Local (To_Rep_Name);
         end;
      end if;

      declare
         Sbst : constant W_Clone_Substitution_Array :=
           (1 =>
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => To_Name (WNE_Array_Component_Type),
                 Image     => Get_Name (Symbols.Comp_Ty)),
            2 =>
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symb => NID ("to_rep")),
                 Image     => Get_Name (To_Rep_Name)),
            3 =>
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name (Symb => NID ("map")),
                 Image     => Get_Name (Symbols.Ty)))
           & Prepare_Indexes_Substitutions
               (Th, Base_Type (Etype (Fst_Idx)), "Index")
           & (1 =>
                New_Clone_Substitution
                  (Kind      => EW_Function,
                   Orig_Name => New_Name (Symb => NID ("get")),
                   Image     => Get_Name (Symbols.Get)),
              2 =>
                New_Clone_Substitution
                  (Kind      => EW_Function,
                   Orig_Name => New_Name (Symb => NID ("bool_eq")),
                   Image     => Get_Name (Symbols.Bool_Eq)));

      begin
         if Has_Modular_Integer_Type (Component_Typ)
           and then not Has_No_Bitwise_Operations_Annotation (Component_Typ)
         then
            Emit
              (Th,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        =>
                    (if Base = EW_BitVector_8_Type
                     then Array_BV8_Rep_Comparison_Ax
                     elsif Base = EW_BitVector_16_Type
                     then Array_BV16_Rep_Comparison_Ax
                     elsif Base = EW_BitVector_32_Type
                     then Array_BV32_Rep_Comparison_Ax
                     elsif Base = EW_BitVector_64_Type
                     then Array_BV64_Rep_Comparison_Ax
                     elsif Base = EW_BitVector_128_Type
                     then Array_BV128_Rep_Comparison_Ax
                     else raise Program_Error),
                  As_Name       => No_Symbol,
                  Substitutions => Sbst));
         else
            Emit
              (Th,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        => Array_Int_Rep_Comparison_Ax,
                  As_Name       => No_Symbol,
                  Substitutions => Sbst));
         end if;
      end;

      Close_Theory (Th, Kind => Definition_Theory);
   end Declare_Comparison_Symbols;

   -------------------------------
   -- Declare_Equality_Function --
   -------------------------------

   procedure Declare_Equality_Function
     (E : Entity_Id; Th : Theory_UC; Symbols : M_Array_Type)
   is
      Map_Ty   : constant W_Type_Id :=
        New_Named_Type (Name => To_Local (Get_Name (Symbols.Ty)));
      A_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Map_Ty);
      B_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "b", Typ => Map_Ty);
      Dim      : constant Positive := Positive (Number_Dimensions (E));
      Idx_Vars : Binder_Array (1 .. Dim);
      --  Binders for quantified index variables.
      --  idx1 idx2 ...

      Args_Lgth : constant Natural := Dim * 2 + 1;
      Args      : Binder_Array (1 .. 2 * Args_Lgth);
      --  Binders for the parameters of the equality function.
      --  a a__first a__last a__first_2 ... b  b__first ...

      A_Indexes : W_Expr_Array (1 .. Dim + 1);
      --  Expressions used to access an element in A.
      --  a idx1 idx2 ...

      B_Indexes : W_Expr_Array (1 .. Dim + 1);
      --  Expressions used to access an element in B.
      --  b (b__first - a__first + idx1) ...

      Range_Cond : W_Pred_Id := True_Pred;
      --  The index variables are in range.
      --  a__first <= idx1 <= a__last /\ ...

      Length_Eq : W_Pred_Id := True_Pred;
      --  The arrays have the same length.
      --  (if a__first <= a__last then a__last - a__first = b__last - b__first
      --   else b__first > b__last) /\ ...

      Index : Node_Id := First_Index (E);
      I     : Positive := 1;

   begin
      --  Store a and b in Args

      Args (1) :=
        Binder_Type'
          (Ada_Node => Empty,
           B_Name   => A_Ident,
           B_Ent    => Null_Entity_Name,
           Mutable  => False,
           Labels   => <>);
      Args (Args_Lgth + 1) :=
        Binder_Type'
          (Ada_Node => Empty,
           B_Name   => B_Ident,
           B_Ent    => Null_Entity_Name,
           Mutable  => False,
           Labels   => <>);

      --  Store a and b in their expression array

      A_Indexes (1) := +A_Ident;
      B_Indexes (1) := +B_Ident;

      while Present (Index) loop
         declare
            Typ   : constant W_Type_Id := Base_Why_Type_No_Bool (Index);
            Idx   : constant W_Identifier_Id :=
              New_Temp_Identifier (Base_Name => "idx", Typ => Typ);
            A_Fst : constant W_Identifier_Id :=
              Attr_Append ("a", Attribute_First, I, Typ);
            A_Lst : constant W_Identifier_Id :=
              Attr_Append ("a", Attribute_Last, I, Typ);
            B_Fst : constant W_Identifier_Id :=
              Attr_Append ("b", Attribute_First, I, Typ);
            B_Lst : constant W_Identifier_Id :=
              Attr_Append ("b", Attribute_Last, I, Typ);

         begin
            --  Store the new index in the quantified variables

            Idx_Vars (I) :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => Idx,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);

            --  Store the first and last bounds of a and b in Args

            Args (2 * I) :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => A_Fst,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);
            Args (2 * I + 1) :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => A_Lst,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);
            Args (Args_Lgth + 2 * I) :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => B_Fst,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);
            Args (Args_Lgth + 2 * I + 1) :=
              Binder_Type'
                (Ada_Node => Empty,
                 B_Name   => B_Lst,
                 B_Ent    => Null_Entity_Name,
                 Mutable  => False,
                 Labels   => <>);

            --  Compute the expressions of the index accesses

            A_Indexes (I + 1) := +Idx;
            B_Indexes (I + 1) :=
              New_Discrete_Add
                (EW_Term,
                 New_Discrete_Substract (EW_Term, +B_Fst, +A_Fst),
                 +Idx);

            --  Compute the range condition

            Range_Cond :=
              +New_And_Expr
                 (Left   => +Range_Cond,
                  Right  =>
                    New_Range_Expr
                      (Domain => EW_Pred,
                       Low    => +A_Fst,
                       High   => +A_Lst,
                       Expr   => +Idx),
                  Domain => EW_Pred);

            --  Compute the equality of lengths

            Length_Eq :=
              +New_And_Expr
                 (Left   => +Length_Eq,
                  Right  =>
                    New_Conditional
                      (Domain    => EW_Pred,
                       Condition =>
                         New_Comparison
                           (Symbol =>
                              (if Typ = EW_Int_Type
                               then Int_Infix_Le
                               elsif Why_Type_Is_BitVector (Typ)
                               then MF_BVs (Typ).Ule
                               else raise Program_Error),
                            Left   => +A_Fst,
                            Right  => +A_Lst,
                            Domain => EW_Pred),
                       Then_Part =>
                         New_And_Expr
                           (Left   =>
                              New_Comparison
                                (Symbol =>
                                   (if Typ = EW_Int_Type
                                    then Int_Infix_Le
                                    elsif Why_Type_Is_BitVector (Typ)
                                    then MF_BVs (Typ).Ule
                                    else raise Program_Error),
                                 Left   => +B_Fst,
                                 Right  => +B_Lst,
                                 Domain => EW_Pred),
                            Right  =>
                              New_Comparison
                                (Symbol => Why_Eq,
                                 Left   =>
                                   New_Discrete_Substract
                                     (EW_Pred, +A_Lst, +A_Fst),
                                 Right  =>
                                   New_Discrete_Substract
                                     (EW_Pred, +B_Lst, +B_Fst),
                                 Domain => EW_Pred),
                            Domain => EW_Pred),
                       Else_Part =>
                         New_Comparison
                           (Symbol =>
                              (if Typ = EW_Int_Type
                               then Int_Infix_Gt
                               elsif Why_Type_Is_BitVector (Typ)
                               then MF_BVs (Typ).Ugt
                               else raise Program_Error),
                            Left   => +B_Fst,
                            Right  => +B_Lst,
                            Domain => EW_Pred),
                       Typ       => EW_Bool_Type),
                  Domain => EW_Pred);

            Next_Index (Index);
            I := I + 1;
         end;
      end loop;

      --  If the type is limited, still declare an abstract placeholder for
      --  the equality function which will be used to clone the array theory.

      if Is_Inherently_Limited_Type (E) then

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (Symbols.Bool_Eq),
               Binders     => Args,
               Return_Type => +EW_Bool_Type,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set));

      --  Emit:
      --  function bool_eq (a : map) (a__first : t1) ... (b : map) ... : bool =
      --    if ((if a__first <= a__last
      --         then a__last - a__first = b__last - b__first
      --         else b__first > b__last) /\ ...) /\
      --        (forall idx1 : t1, idx2 : t2 ...
      --           (a__first <= idx1 <= a__last /\ ...) ->
      --            <ada_eq> (get a idx1 ...)
      --                     (get b (b__first - a__first + idx1) ...))
      --    then True else False
      --  where <ada_eq> is user_eq in the component type is a record type and
      --  bool_eq otherwise.

      else

         declare
            C_Type   : constant Entity_Id := Retysp (Component_Type (E));
            W_Ty     : constant W_Type_Id :=
              EW_Abstract (C_Type, Relaxed_Init => Has_Relaxed_Init (C_Type));
            Get_Name : constant W_Identifier_Id := To_Local (Symbols.Get);
            Eq_Name  : constant W_Identifier_Id := To_Local (Symbols.Bool_Eq);
            Def      : W_Pred_Id :=
              +New_Ada_Equality
                 (Typ    => C_Type,
                  Domain => EW_Pred,
                  Left   =>
                    Insert_Simple_Conversion
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Call (Empty, EW_Term, Get_Name, A_Indexes, W_Ty),
                       To       => EW_Abstract (C_Type)),
                  Right  =>
                    Insert_Simple_Conversion
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Expr     =>
                         New_Call (Empty, EW_Term, Get_Name, B_Indexes, W_Ty),
                       To       => EW_Abstract (C_Type)));
         begin

            Def :=
              New_Conditional
                (Condition => +Range_Cond,
                 Then_Part => +Def,
                 Typ       => EW_Bool_Type);

            Def := New_Universal_Quantif (Binders => Idx_Vars, Pred => +Def);

            Def :=
              +New_And_Expr
                 (Left => +Length_Eq, Right => +Def, Domain => EW_Pred);

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Eq_Name,
                  Binders     => Args,
                  Return_Type => +EW_Bool_Type,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Def         => +Def));

            --  This axiom is provable from the definition of bool_eq. We
            --  supply it to help E-matching when a_first is different from
            --  b_first.

            declare
               Rev_Args : constant Binder_Array :=
                 Args (Args_Lgth + 1 .. 2 * Args_Lgth) & Args (1 .. Args_Lgth);
               Rev_Call : constant W_Expr_Id :=
                 New_Call (Empty, EW_Term, Eq_Name, Rev_Args, EW_Bool_Type);
            begin
               Emit
                 (Th,
                  New_Guarded_Axiom
                    (Name    => NID ("bool_eq_rev"),
                     Binders => Args,
                     Pre     =>
                       +New_Comparison
                          (Symbol => Why_Eq,
                           Left   => Rev_Call,
                           Right  => +True_Term,
                           Domain => EW_Pred),
                     Def     => Def,
                     Dep     =>
                       New_Axiom_Dep
                         (Name => Eq_Name, Kind => EW_Axdep_Func)));
            end;
         end;
      end if;
   end Declare_Equality_Function;

   -------------------------------
   -- Declare_Getter_And_Setter --
   -------------------------------

   procedure Declare_Getter_And_Setter
     (Th       : Theory_UC;
      E        : Entity_Id;
      Arr_Ty   : W_Type_Id;
      Comp_Ty  : W_Type_Id;
      Get_Symb : W_Identifier_Id;
      Set_Symb : W_Identifier_Id)
   is
      Arr_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "arr", Typ => Arr_Ty);
      Arr_Binder  : constant Binder_Type :=
        (B_Name => Arr_Ident, others => <>);
      Comp_Binder : constant Binder_Type :=
        (B_Name => New_Identifier (Name => "comp", Typ => Comp_Ty),
         others => <>);
      Nb_Dim      : constant Positive := Positive (Number_Dimensions (E));
      I_Binders   : Binder_Array (1 .. Nb_Dim);

   begin
      for I in I_Binders'Range loop
         I_Binders (I) :=
           (B_Name =>
              New_Identifier
                (Name => Append_Num ("i", I),
                 Typ  => Nth_Index_Rep_Type_No_Bool (E, I)),
            others => <>);
      end loop;

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => Get_Symb,
            Binders     => Binder_Array'(Arr_Binder & I_Binders),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Comp_Ty));

      declare
         J_Binders : Binder_Array (1 .. Nb_Dim);
         Distinct  : W_Pred_Array (1 .. Nb_Dim);

      begin
         for I in J_Binders'Range loop
            J_Binders (I) :=
              (B_Name =>
                 New_Identifier
                   (Name => Append_Num ("j", I),
                    Typ  => Nth_Index_Rep_Type_No_Bool (E, I)),
               others => <>);
            Distinct (I) :=
              New_Comparison
                (Symbol => Why_Neq,
                 Left   => +J_Binders (I).B_Name,
                 Right  => +I_Binders (I).B_Name);
         end loop;

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => Set_Symb,
               Binders     =>
                 Binder_Array'(Arr_Binder & I_Binders & Comp_Binder),
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Arr_Ty));

         declare
            Set_Call  : constant W_Term_Id :=
              New_Call
                (Name    => Set_Symb,
                 Binders =>
                   Binder_Array'(Arr_Binder & I_Binders & Comp_Binder),
                 Typ     => Arr_Ty);
            Get_Eq    : constant W_Term_Id :=
              New_Call
                (Name => Get_Symb,
                 Args =>
                   W_Expr_Array'
                     (+Set_Call & Get_Args_From_Binders (I_Binders, False)));
            Get_Neq_1 : constant W_Term_Id :=
              New_Call
                (Name => Get_Symb,
                 Args =>
                   W_Expr_Array'
                     (+Set_Call & Get_Args_From_Binders (J_Binders, False)));
            Get_Neq_2 : constant W_Term_Id :=
              New_Call (Name => Get_Symb, Binders => Arr_Binder & J_Binders);
         begin
            Emit
              (Th,
               New_Guarded_Axiom
                 (Name     => NID ("__set__eq"),
                  Binders  =>
                    Binder_Array'(Arr_Binder & I_Binders & Comp_Binder),
                  Triggers =>
                    New_Triggers
                      (Triggers =>
                         (1 => New_Trigger (Terms => (1 => +Get_Eq)))),
                  Def      =>
                    New_Comparison
                      (Symbol => Why_Eq,
                       Left   => Get_Eq,
                       Right  => +Comp_Binder.B_Name),
                  Dep      =>
                    New_Axiom_Dep (Name => Set_Symb, Kind => EW_Axdep_Func)));
            Emit
              (Th,
               New_Guarded_Axiom
                 (Name     => NID ("__set__neq"),
                  Binders  =>
                    Binder_Array'
                      (Arr_Binder & I_Binders & J_Binders & Comp_Binder),
                  Triggers =>
                    New_Triggers
                      (Triggers =>
                         (1 => New_Trigger (Terms => (1 => +Get_Neq_1)),
                          2 =>
                            New_Trigger (Terms => (+Set_Call, +Get_Neq_2)))),
                  Def      =>
                    New_Conditional
                      (Condition => New_Or_Pred (Distinct),
                       Then_Part =>
                         New_Comparison
                           (Symbol => Why_Eq,
                            Left   => Get_Neq_1,
                            Right  => Get_Neq_2)),
                  Dep      =>
                    New_Axiom_Dep (Name => Set_Symb, Kind => EW_Axdep_Func)));
         end;
      end;
   end Declare_Getter_And_Setter;

   ------------------------------------
   -- Declare_Init_Wrapper_For_Array --
   ------------------------------------

   procedure Declare_Init_Wrapper_For_Array (Th : Theory_UC; E : Entity_Id) is
   begin
      Declare_Ada_Array (Th => Th, E => E, Relaxed_Init => True);
   end Declare_Init_Wrapper_For_Array;

   ---------------------------------------
   -- Declare_Logical_Operation_Symbols --
   ---------------------------------------

   procedure Declare_Logical_Operation_Symbols
     (E : Entity_Id; Module : W_Module_Id; Symbols : M_Array_Type)
   is
      Component_Typ : constant Entity_Id := Component_Type (E);
      Th            : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module,
           Comment =>
             "Module for axiomatizing logical operations for the array theory"
             & " associated to type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  For Boolean, use the module Standard_Array_Logical_Op_Axioms

      if Is_Standard_Boolean_Type (Component_Typ) then

         Emit
           (Th,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               Origin        => Standard_Array_Logical_Ax,
               As_Name       => No_Symbol,
               Substitutions =>
                 Prepare_Standard_Array_Logical_Substitutions
                   (Th, E, Symbols)));

      --  Otherwise, clone the specific module Subtype_Array_Logical_Op_Axioms
      --  which needs additional parameters to_int and of_int.
      --  If Component_Typ has relaxed initialization, we need to declare
      --  these conversion functions first.

      elsif Has_Relaxed_Init (Component_Typ) then
         declare
            Comp_Ty : constant W_Type_Id :=
              EW_Abstract (Component_Typ, Relaxed_Init => True);
            A_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "a", Typ => Comp_Ty);
            I_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "i", Typ => EW_Int_Type);
            To_Int  : constant W_Name_Id := New_Name (Symb => NID ("to_int"));
            Of_Int  : constant W_Name_Id := New_Name (Symb => NID ("of_int"));

         begin
            --  Declare to_int and of_int functions which convert the wrapper
            --  type to a mathematical integer and backward.

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    New_Identifier
                      (Name => To_Int, Domain => EW_Term, Typ => EW_Int_Type),
                  Binders     =>
                    Binder_Array'(1 => (B_Name => A_Ident, others => <>)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type,
                  Def         =>
                    Insert_Simple_Conversion
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Expr     => +A_Ident,
                       To       => EW_Int_Type)));
            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    New_Identifier
                      (Name => Of_Int, Domain => EW_Term, Typ => Comp_Ty),
                  Binders     =>
                    Binder_Array'(1 => (B_Name => I_Ident, others => <>)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => Comp_Ty,
                  Def         =>
                    Insert_Simple_Conversion
                      (Ada_Node => Empty,
                       Domain   => EW_Term,
                       Expr     => +I_Ident,
                       To       => Comp_Ty)));

            --  Clone the module with the new of_int and to_int wrappers. This
            --  generates the following axioms for each logical operation:
            --    forall i : index_typ.
            --       get result i =
            --         to_wrapper (op (of_wrapper (get a i))
            --                        (of_wrapper (get b i)))

            Emit
              (Th,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        => Subtype_Array_Logical_Ax,
                  As_Name       => No_Symbol,
                  Substitutions =>
                    (Prepare_Standard_Array_Logical_Substitutions
                       (Th, E, Symbols)
                     & (1 =>
                          New_Clone_Substitution
                            (Kind      => EW_Type_Subst,
                             Orig_Name => To_Name (WNE_Array_Component_Type),
                             Image     => Get_Name (Symbols.Comp_Ty)),
                        2 =>
                          New_Clone_Substitution
                            (Kind      => EW_Function,
                             Orig_Name => To_Int,
                             Image     => To_Int),
                        3 =>
                          New_Clone_Substitution
                            (Kind      => EW_Function,
                             Orig_Name => Of_Int,
                             Image     => Of_Int)))));
         end;

      --  Otherwise, we can use the component type conversion functions
      --  directly.

      else
         Emit
           (Th,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               Origin        => Subtype_Array_Logical_Ax,
               As_Name       => No_Symbol,
               Substitutions =>
                 Prepare_Subtype_Array_Logical_Substitutions
                   (Th, E, Symbols)));
      end if;

      Close_Theory (Th, Kind => Definition_Theory);
   end Declare_Logical_Operation_Symbols;

   -------------------------
   -- Declare_Constrained --
   -------------------------

   procedure Declare_Constrained
     (Th         : Theory_UC;
      Und_Ent    : Entity_Id;
      Base_Subst : W_Clone_Substitution_Array)
   is
      Dimension       : constant Pos := Number_Dimensions (Und_Ent);
      Index           : Entity_Id := First_Index (Und_Ent);
      Subst_Per_Index : constant Int := 3;
      Subst           :
        W_Clone_Substitution_Array
          (1 .. Integer (Dimension * Subst_Per_Index));
      Cursor          : Integer := 1;
      Clone           : constant W_Module_Id :=
        Constr_Arrays (Positive (Dimension));

      procedure Declare_Attribute
        (Kind : Why_Name_Enum; Value : Uint; Typ : W_Type_Id);
      --  Declare a constant for the first / last index of the array and
      --  add it to the clone substitution.

      -----------------------
      -- Declare_Attribute --
      -----------------------

      procedure Declare_Attribute
        (Kind : Why_Name_Enum; Value : Uint; Typ : W_Type_Id)
      is
         Attr_Name : constant W_Name_Id := To_Local (E_Symb (Und_Ent, Kind));
      begin
         Emit
           (Th,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => New_Identifier (Attr_Name),
               Binders     => (1 .. 0 => <>),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => Typ,
               Def         =>
                 New_Discrete_Constant (Value => Value, Typ => Typ)));
         Subst (Cursor) :=
           New_Clone_Substitution
             (Kind => EW_Function, Orig_Name => Attr_Name, Image => Attr_Name);
         Cursor := Cursor + 1;
      end Declare_Attribute;

      --  Start of processing for Declare_Constrained

   begin
      if Ekind (Und_Ent) = E_String_Literal_Subtype then
         pragma
           Assert
             (Has_Array_Type (Etype (Und_Ent))
                and then Ekind (Etype (Und_Ent)) /= E_String_Literal_Subtype);
         declare
            Low  : constant Uint :=
              Expr_Value (String_Literal_Low_Bound (Und_Ent));
            R_Ty : constant W_Type_Id :=
              Base_Why_Type_No_Bool
                (Base_Type
                   (Retysp (Etype (First_Index (Retysp (Etype (Und_Ent)))))));
         begin
            Declare_Attribute (WNE_Attr_First (1), Low, R_Ty);
            Declare_Attribute
              (WNE_Attr_Last (1),
               String_Literal_Length (Und_Ent) + Low - 1,
               R_Ty);

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name =>
                   New_Name (Symb => NID (Append_Num ("index_rep_type", 1))),
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
                  R_Ty : constant W_Type_Id :=
                    Base_Why_Type_No_Bool (Base_Type (Retysp (Etype (Index))));
               begin
                  Declare_Attribute
                    (WNE_Attr_First (Count),
                     Expr_Value (Low_Bound (Rng)),
                     R_Ty);
                  Declare_Attribute
                    (WNE_Attr_Last (Count),
                     Expr_Value (High_Bound (Rng)),
                     R_Ty);

                  Subst (Cursor) :=
                    New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name =>
                         New_Name
                           (Symb =>
                              NID (Append_Num ("index_rep_type", Count))),
                       Image     => Get_Name (R_Ty));
                  Cursor := Cursor + 1;

                  Count := Count + 1;
                  Next_Index (Index);
               end;
            end loop;
         end;
      end if;

      Emit
        (Th,
         New_Clone_Declaration
           (Theory_Kind   => EW_Module,
            Clone_Kind    => EW_Export,
            As_Name       => No_Symbol,
            Origin        => Clone,
            Substitutions => Base_Subst & Subst));
   end Declare_Constrained;

   ---------------------------
   -- Declare_Unconstrained --
   ---------------------------

   procedure Declare_Unconstrained
     (Th             : Theory_UC;
      Why3_Type_Name : W_Name_Id;
      Und_Ent        : Entity_Id;
      Base_Subst     : W_Clone_Substitution_Array)
   is
      Dimension       : constant Pos := Number_Dimensions (Und_Ent);
      Subst_Per_Index : constant Int := 7;
      Subst           :
        W_Clone_Substitution_Array
          (1 .. Integer (Dimension * Subst_Per_Index));
      Cursor          : Integer := 1;
      Index           : Node_Id := First_Index (Und_Ent);
      Dim_Count       : Integer := 1;
      Clone           : constant W_Module_Id :=
        Unconstr_Arrays (Positive (Dimension));

   begin
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
                 Orig_Name =>
                   New_Name
                     (Symb => NID (Append_Num ("index_base_type", Dim_Count))),
                 Image     => Ident_Of_Ada_Type (B_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name =>
                   New_Name
                     (Symb => NID (Append_Num ("index_rep_type", Dim_Count))),
                 Image     => Get_Name (R_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name =>
                   New_Name (Symb => NID (Append_Num ("to_rep", Dim_Count))),
                 Image     =>
                   Get_Name (Conversion_Name (From => +B_Type, To => R_Ty)));
            Cursor := Cursor + 1;

            if R_Ty = EW_Int_Type then
               declare
                  Id_Id : constant W_Identifier_Id :=
                    New_Identifier
                      (Name => "index_" & Image (Dim_Count, 1) & "_id");
                  X_Id  : constant W_Identifier_Id :=
                    New_Identifier (Name => "x", Typ => R_Ty);
               begin
                  Emit
                    (Th,
                     Why.Gen.Binders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Id_Id,
                        Binders     => (1 => (B_Name => X_Id, others => <>)),
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Def         => +X_Id,
                        Return_Type => R_Ty));

                  Subst (Cursor) :=
                    New_Clone_Substitution
                      (Kind      => EW_Function,
                       Orig_Name =>
                         New_Name
                           (Symb =>
                              NID (Append_Num ("rep_to_int", Dim_Count))),
                       Image     => Get_Name (Id_Id));
               end;
            else
               Subst (Cursor) :=
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name =>
                      New_Name
                        (Symb => NID (Append_Num ("rep_to_int", Dim_Count))),
                    Image     =>
                      Get_Name
                        (Conversion_Name (From => R_Ty, To => EW_Int_Type)));
            end if;
            Cursor := Cursor + 1;

            --  Range on base type only used for empty array (e.g. 12..7)
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name =>
                   To_Local
                     (E_Symb (Und_Ent, WNE_Array_Base_Range_Pred (Dim_Count))),
                 Image     => Get_Name (Range_Pred_Name (B_Ty)));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name =>
                   To_Local
                     (E_Symb
                        (Und_Ent, WNE_Index_Dynamic_Property (Dim_Count))),
                 Image     => Get_Name (Dynamic_Prop_Name (Ind_Ty)));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name =>
                   New_Name
                     (Symb => NID (Append_Num ("index_rep_le", Dim_Count))),
                 Image     =>
                   Get_Name
                     (if Has_Modular_Integer_Type (Ind_Ty)
                        and then not Has_No_Bitwise_Operations_Annotation
                                       (Ind_Ty)
                      then MF_BVs (R_Ty).Ule
                      else Int_Infix_Le));
            Cursor := Cursor + 1;
         end;
         Dim_Count := Dim_Count + 1;
         Next_Index (Index);
      end loop;

      Emit
        (Th,
         New_Clone_Declaration
           (Theory_Kind   => EW_Module,
            Clone_Kind    => EW_Export,
            As_Name       => No_Symbol,
            Origin        => Clone,
            Substitutions => Base_Subst & Subst));
      --  Declare the abstract type of the unconstrained array and mark
      --  function "to_array" as projection (from this type to why3 map type)
      Emit
        (Th,
         New_Type_Decl
           (Why3_Type_Name,
            Alias => New_Named_Type (To_String (WNE_Array_Type))));
      Emit_Projection_Metas (Th, "to_array");
      Emit_Projection_Metas (Th, "first");
      Emit_Projection_Metas (Th, "last");
      --  Dim_Count is actually nb of dimention + 1 here
      for I in 2 .. Dim_Count - 1 loop
         Emit_Projection_Metas (Th, "first_" & Image (I, 1));
         Emit_Projection_Metas (Th, "last_" & Image (I, 1));
      end loop;
   end Declare_Unconstrained;

   --------------------
   -- Get_Array_Attr --
   --------------------

   function Get_Array_Attr
     (Domain : EW_Terms;
      Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive;
      Params : Transformation_Params := Body_Params;
      Typ    : W_Type_Id := EW_Int_Type) return W_Term_Id is
   begin
      if Attr in Attribute_First | Attribute_Last then
         declare
            Index_Type : constant Entity_Id := Nth_Index_Type (Ty, Dim);
         begin
            return
              Insert_Simple_Conversion
                (Expr =>
                   +New_Attribute_Expr
                      (Ty     => Index_Type,
                       Domain => Domain,
                       Attr   => Attr,
                       Params => Params),
                 To   => Nth_Index_Rep_Type_No_Bool (Ty, Dim));
         end;

      elsif Is_Static_Array_Type (Ty) then
         pragma Assert (Is_Constrained (Ty));
         return
           New_Discrete_Constant
             (Value => Static_Array_Length (Ty, Dim), Typ => Typ);

      else
         pragma Assert (Is_Constrained (Ty));
         return +Build_Length_Expr (Domain, Ty, Dim, Typ);
      end if;
   end Get_Array_Attr;

   function Get_Array_Attr
     (Expr : W_Term_Id;
      Attr : Attribute_Id;
      Dim  : Positive;
      Typ  : W_Type_Id := EW_Int_Type) return W_Term_Id
   is
      W_Ty         : constant W_Type_Id := Get_Type (+Expr);
      Ty           : constant Entity_Id := Get_Ada_Node (+W_Ty);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (W_Ty);
   begin
      --  If the type is constrained, just use the type information

      if Is_Static_Array_Type (Ty) then
         return Get_Array_Attr (EW_Term, Ty, Attr, Dim, Typ => Typ);

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
                   (Name => E_Symb (Ty, Enum, Relaxed_Init),
                    Args => (1 => +Expr),
                    Typ  => Nth_Index_Rep_Type_No_Bool (Ty, Dim));
            end;

         elsif Typ = EW_Int_Type then
            return
              New_Call
                (Name => E_Symb (Ty, WNE_Attr_Length (Dim), Relaxed_Init),
                 Args => (1 => +Expr),
                 Typ  => EW_Int_Type);

         else
            return
              +Build_Length_Expr
                 (Domain => EW_Term, Expr => +Expr, Dim => Dim, Typ => Typ);
         end if;
      end if;
   end Get_Array_Attr;

   function Get_Array_Attr
     (Item : Item_Type;
      Attr : Attribute_Id;
      Dim  : Positive;
      Typ  : W_Type_Id := EW_Int_Type) return W_Term_Id is
   begin
      case Item.Kind is
         when Regular =>
            return Get_Array_Attr (+Item.Main.B_Name, Attr, Dim, Typ);

         when UCArray =>
            case Attr is
               when Attribute_First  =>
                  return +Item.Bounds (Dim).First;

               when Attribute_Last   =>
                  return +Item.Bounds (Dim).Last;

               when Attribute_Length =>
                  return
                    +Build_Length_Expr
                       (Domain => EW_Term,
                        First  => +Item.Bounds (Dim).First,
                        Last   => +Item.Bounds (Dim).Last,
                        Typ    => Typ);

               when others           =>
                  raise Program_Error;
            end case;

         when others  =>
            raise Program_Error;
      end case;
   end Get_Array_Attr;

   -------------------------------
   -- Get_Array_Conversion_Name --
   -------------------------------

   function Get_Array_Conversion_Name
     (From, To : Entity_Id; Relaxed_Init : Boolean := False)
      return W_Identifier_Id
   is (M_Arrays_Conversion (Get_Array_Theory_Name (From, Relaxed_Init))
         (Get_Array_Theory_Name (To, Relaxed_Init)));

   ---------------------------------
   -- Get_Array_Of_Wrapper_Name --
   ---------------------------------

   function Get_Array_Of_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
   is (M_Arrays_Conversion (Get_Array_Theory_Name (E, True))
         (Get_Array_Theory_Name (E, False)));

   ----------------------
   -- Get_Array_Theory --
   ----------------------

   function Get_Array_Theory
     (E : Entity_Id; Relaxed_Init : Boolean := False) return M_Array_Type
   is (M_Arrays (Get_Array_Theory_Name (E, Relaxed_Init)));

   -------------------------------
   -- Get_Array_To_Wrapper_Name --
   -------------------------------

   function Get_Array_To_Wrapper_Name (E : Entity_Id) return W_Identifier_Id
   is (M_Arrays_Conversion (Get_Array_Theory_Name (E, False))
         (Get_Array_Theory_Name (E, True)));

   ------------------------
   -- Get_Array_Theory_1 --
   ------------------------

   function Get_Array_Theory_1
     (E : Entity_Id; Relaxed_Init : Boolean := False) return M_Array_1_Type
   is (M_Arrays_1 (Get_Array_Theory_Name (E, Relaxed_Init)));

   -----------------------------
   -- Get_Array_Theory_1_Comp --
   -----------------------------

   function Get_Array_Theory_1_Comp (E : Entity_Id) return M_Array_1_Comp_Type
   is (M_Arrays_1_Comp (Get_Array_Theory_Name (E)));

   --------------------------------
   -- Get_Array_Theory_1_Bool_Op --
   --------------------------------

   function Get_Array_Theory_1_Bool_Op
     (E : Entity_Id) return M_Array_1_Bool_Op_Type
   is (M_Arrays_1_Bool_Op (Get_Array_Theory_Name (E)));

   ---------------------------
   -- Get_Array_Theory_Name --
   ---------------------------

   function Get_Array_Theory_Name
     (E : Entity_Id; Relaxed_Init : Boolean := False) return Symbol
   is
      Name      : Unbounded_String :=
        To_Unbounded_String (To_String (WNE_Array_Prefix));
      Ty        : constant Entity_Id := Retysp (E);
      Type_Name : Unbounded_String;
      Index     : Node_Id := First_Index (Ty);
      Dim       : constant Positive := Positive (Number_Dimensions (Ty));
   begin
      if Ekind (Ty) = E_String_Literal_Subtype then
         return Get_Array_Theory_Name (Etype (Ty), Relaxed_Init);
      end if;

      for I in 1 .. Dim loop
         if Has_Modular_Integer_Type (Etype (Index))
           and then not Has_No_Bitwise_Operations_Annotation (Etype (Index))
         then
            Type_Name :=
              To_Unbounded_String
                (To_String (WNE_Array_BV_Suffix)
                 & Image
                     (Integer
                        (UI_To_Int (Modular_Size (Retysp (Etype (Index))))),
                      1));
         else
            Type_Name :=
              To_Unbounded_String (To_String (WNE_Array_Int_Suffix));
         end if;

         Name := Name & Type_Name;

         Next_Index (Index);
      end loop;

      Type_Name :=
        (To_Unbounded_String
           ("__"
            & Capitalize_First (Full_Name (Retysp (Component_Type (Ty))))));
      Name := Name & Type_Name;

      if Relaxed_Init then
         Name := Name & To_String (WNE_Init_Wrapper_Suffix);
      end if;

      return NID (To_String (Name));
   end Get_Array_Theory_Name;

   ----------------------
   -- New_Array_Access --
   ----------------------

   function New_Array_Access
     (Ada_Node : Node_Id := Empty;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Domain   : EW_Domain) return W_Expr_Id
   is
      Why_Ty       : constant W_Type_Id := Get_Type (Ar);
      Ty_Entity    : constant Entity_Id := Get_Ada_Node (+Why_Ty);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Why_Ty);
      Name         : constant W_Identifier_Id :=
        Get_Array_Theory (Ty_Entity, Relaxed_Init).Get;
      Elts         : W_Expr_Id;
      Comp_Ty      : constant Entity_Id := Retysp (Component_Type (Ty_Entity));

   begin
      if Is_Static_Array_Type (Ty_Entity) then
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
           Typ      =>
             EW_Abstract
               (Comp_Ty,
                Relaxed_Init =>
                  Has_Relaxed_Init (Comp_Ty) or else Relaxed_Init));
   end New_Array_Access;

   --------------------------
   -- New_Array_Range_Expr --
   --------------------------

   function New_Array_Range_Expr
     (Index_Expr : W_Term_Id;
      Array_Expr : W_Term_Id;
      Domain     : EW_Domain;
      Dim        : Positive) return W_Expr_Id is
   begin
      return
        New_Range_Expr
          (Domain => Domain,
           Low    =>
             Insert_Conversion_To_Rep_No_Bool
               (EW_Term,
                +Get_Array_Attr
                   (Expr => Array_Expr, Attr => Attribute_First, Dim => Dim)),
           High   =>
             Insert_Conversion_To_Rep_No_Bool
               (EW_Term,
                +Get_Array_Attr
                   (Expr => Array_Expr, Attr => Attribute_Last, Dim => Dim)),
           Expr   => Insert_Conversion_To_Rep_No_Bool (EW_Term, +Index_Expr));
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
      W_Ty         : constant W_Type_Id := Get_Type (Ar);
      Ty_Entity    : constant Entity_Id := Get_Ada_Node (+W_Ty);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (W_Ty);
      Name         : constant W_Identifier_Id :=
        Get_Array_Theory (Ty_Entity, Relaxed_Init).Set;
      Val          : constant W_Expr_Id :=
        (if Has_Relaxed_Init (Component_Type (Ty_Entity)) or else Relaxed_Init
         then
           Insert_Simple_Conversion
             (Ada_Node => Ada_Node,
              Domain   => Domain,
              Expr     => Value,
              To       =>
                EW_Abstract (Component_Type (Ty_Entity), Relaxed_Init => True))
         else Value);
   begin
      if Is_Static_Array_Type (Ty_Entity) then
         return
           New_Call
             (Ada_Node => Ada_Node,
              Domain   => Domain,
              Name     => Name,
              Args     => (1 => +Ar) & Index & (1 => +Val),
              Typ      => W_Ty);
      else
         declare
            Args      : constant W_Expr_Array :=
              (1 => Array_Convert_To_Base (Domain => Domain, Ar => Ar))
              & Index
              & (1 => +Val);
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
                         Field  =>
                           E_Symb (Ty_Entity, WNE_Array_Elts, Relaxed_Init),
                         Value  => Array_Upd)),
                 Typ     => W_Ty);
         end;
      end if;
   end New_Array_Update;

   -------------------------
   -- New_Bounds_Equality --
   -------------------------

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id; Right_Bounds : W_Expr_Array; Dim : Positive)
      return W_Pred_Id
   is
      Result : W_Pred_Id := True_Pred;
   begin
      for I in 1 .. Dim loop
         Result :=
           New_And_Pred
             (Conjuncts =>
                (1 => Result,

                 --  <left_arr>.first__I = <right_arr>.first__I

                 2 =>
                   New_Comparison
                     (Symbol => Why_Eq,
                      Left   =>
                        +Insert_Conversion_To_Rep_No_Bool
                           (EW_Term,
                            +Get_Array_Attr
                               (Expr => Left_Arr,
                                Attr => Attribute_First,
                                Dim  => I)),
                      Right  => +Right_Bounds (2 * I - 1)),

                 --  <left_arr>.last__I = <right_arr>.last__I

                 3 =>
                   New_Comparison
                     (Symbol => Why_Eq,
                      Left   =>
                        +Insert_Conversion_To_Rep_No_Bool
                           (EW_Term,
                            +Get_Array_Attr
                               (Expr => Left_Arr,
                                Attr => Attribute_Last,
                                Dim  => I)),
                      Right  => +Right_Bounds (2 * I))));
      end loop;

      return +Result;
   end New_Bounds_Equality;

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id; Right_Arr : W_Term_Id; Dim : Positive)
      return W_Pred_Id
   is
      Right_Bounds : W_Expr_Array (1 .. 2 * Dim);
      Count        : Positive := 1;
   begin
      for I in 1 .. Dim loop
         Add_Attr_Arg
           (EW_Term, Right_Bounds, +Right_Arr, Attribute_First, I, Count);
         Add_Attr_Arg
           (EW_Term, Right_Bounds, +Right_Arr, Attribute_Last, I, Count);
      end loop;

      return New_Bounds_Equality (Left_Arr, Right_Bounds, Dim);
   end New_Bounds_Equality;

   function New_Bounds_Equality
     (Left_Arr : W_Term_Id;
      Right_Ty : Entity_Id;
      Params   : Transformation_Params := Body_Params) return W_Pred_Id
   is
      Dim          : constant Positive :=
        Positive (Number_Dimensions (Right_Ty));
      Right_Bounds : W_Expr_Array (1 .. 2 * Dim);
      Count        : Positive := 1;
   begin
      for I in 1 .. Dim loop
         Add_Attr_Arg
           (EW_Term,
            Right_Bounds,
            Right_Ty,
            Attribute_First,
            I,
            Count,
            Params);
         Add_Attr_Arg
           (EW_Term, Right_Bounds, Right_Ty, Attribute_Last, I, Count, Params);
      end loop;

      return New_Bounds_Equality (Left_Arr, Right_Bounds, Dim);
   end New_Bounds_Equality;

   ---------------------
   -- New_Concat_Call --
   ---------------------

   function New_Concat_Call
     (Domain             : EW_Domain;
      Args               : W_Expr_Array;
      Typ                : W_Type_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean) return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Get_Array_Theory_1 (Get_Ada_Node (+Typ), Relaxed_Init).Concat
               (Is_Component_Left, Is_Component_Right),
           Args   => Args,
           Typ    => Typ);
   end New_Concat_Call;

   --------------------
   -- New_Const_Call --
   --------------------

   function New_Const_Call
     (Domain : EW_Domain;
      Elt    : W_Expr_Id;
      Bounds : W_Expr_Array;
      Typ    : W_Type_Id) return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
      E            : constant Entity_Id := Get_Ada_Node (+Typ);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => Get_Array_Theory (E, Relaxed_Init).Const,
           Args   => Elt & Bounds,
           Typ    => EW_Split (E, Relaxed_Init => Relaxed_Init));
   end New_Const_Call;

   ---------------------------
   --  New_Dynamic_Property --
   ---------------------------

   function New_Dynamic_Property
     (Domain : EW_Domain;
      Ty     : Entity_Id;
      Args   : W_Expr_Array;
      Params : Transformation_Params := Body_Params) return W_Expr_Id
   is
      Rep_Ty    : constant Entity_Id := Retysp (Ty);
      Dim       : constant Positive := Positive (Number_Dimensions (Rep_Ty));
      Call_Args : W_Expr_Array (1 .. 4 * Dim);

   begin
      pragma Assert (Args'Length = 2 * Dim);
      for Count in 0 .. Dim - 1 loop
         declare
            W_Typ      : constant W_Type_Id :=
              Nth_Index_Rep_Type_No_Bool (E => Rep_Ty, Dim => Count + 1);
            First_Expr : constant W_Term_Id :=
              Insert_Simple_Conversion
                (Expr =>
                   Get_Array_Attr
                     (Domain => Term_Domain (Domain),
                      Ty     => Rep_Ty,
                      Attr   => Attribute_First,
                      Dim    => Count + 1,
                      Params => Params),
                 To   => W_Typ);
            Last_Expr  : constant W_Term_Id :=
              Insert_Simple_Conversion
                (Expr =>
                   Get_Array_Attr
                     (Domain => Term_Domain (Domain),
                      Ty     => Rep_Ty,
                      Attr   => Attribute_Last,
                      Dim    => Count + 1,
                      Params => Params),
                 To   => W_Typ);
            F_Expr     : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => Domain, Expr => Args (2 * Count + 1), To => W_Typ);
            L_Expr     : constant W_Expr_Id :=
              Insert_Simple_Conversion
                (Domain => Domain, Expr => Args (2 * Count + 2), To => W_Typ);
         begin
            Call_Args (4 * Count + 1) := +First_Expr;
            Call_Args (4 * Count + 2) := +Last_Expr;
            Call_Args (4 * Count + 3) := F_Expr;
            Call_Args (4 * Count + 4) := L_Expr;
         end;
      end loop;

      return
        New_Call
          (Domain => Domain,
           Name   => Dynamic_Prop_Name (Rep_Ty),
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
           (Domain => EW_Pred, Symbol => Why_Eq, Left => Left, Right => Right);
   begin
      return Result;
   end New_Element_Equality;

   -------------------------
   -- New_Length_Equality --
   -------------------------

   function New_Length_Equality
     (L_First_E : W_Term_Id;
      L_Last_E  : W_Term_Id;
      R_First_E : W_Term_Id;
      R_Last_E  : W_Term_Id;
      Base_Ty   : W_Type_Id) return W_Pred_Id
   is
      Le_Op  : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type
         then Int_Infix_Le
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Ule
         else raise Program_Error);
      Lt_Op  : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type
         then Int_Infix_Lt
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Ult
         else raise Program_Error);
      Sub_Op : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type
         then Int_Infix_Subtr
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Sub
         else raise Program_Error);

   begin
      --  (if <left_arr>.first_I <= <left_arr>.last_I then
      --     <right_arr>.first_I <= <right_arr>.last_I
      --     /\ <left_arr>.last_I - <left_arr>.first_I =
      --        <right_arr>.last_I - <right_arr>.first_I
      --   else <right_arr>.last_I < <right_arr>.first_I)

      return
        New_Conditional
          (Condition =>
             New_Call
               (Name => Le_Op,
                Args => [+L_First_E, +L_Last_E],
                Typ  => EW_Bool_Type),
           Then_Part =>
             New_And_Pred
               (Left  =>
                  New_Call
                    (Name => Le_Op,
                     Args => [+R_First_E, +R_Last_E],
                     Typ  => EW_Bool_Type),
                Right =>
                  New_Comparison
                    (Symbol => Why_Eq,
                     Left   =>
                       New_Call
                         (Name => Sub_Op,
                          Args => [+L_Last_E, +L_First_E],
                          Typ  => Base_Ty),
                     Right  =>
                       New_Call
                         (Name => Sub_Op,
                          Args => [+R_Last_E, +R_First_E],
                          Typ  => Base_Ty))),
           Else_Part =>
             New_Call
               (Name => Lt_Op,
                Args => [+R_Last_E, +R_First_E],
                Typ  => Base_Ty),
           Typ       => EW_Bool_Type);
   end New_Length_Equality;

   function New_Length_Equality
     (Left_Arr : W_Term_Id; Right_Arr : W_Term_Id; Dim : Positive)
      return W_Pred_Id
   is
      L_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (+Left_Arr));
      R_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (+Right_Arr));
      Is_Static : constant Boolean :=
        Has_Static_Array_Type (L_Ty) and then Has_Static_Array_Type (R_Ty);
      Result    : W_Pred_Id := True_Pred;

   begin
      for I in 1 .. Dim loop

         --  Do not issue checks for statically matching lengths

         if not Is_Static
           or else Static_Array_Length (Retysp (L_Ty), I)
                   /= Static_Array_Length (Retysp (R_Ty), I)
         then
            declare
               Base_Ty : constant W_Type_Id :=
                 Nth_Index_Rep_Type_No_Bool (L_Ty, Dim);
               pragma
                 Assert (Base_Ty = Nth_Index_Rep_Type_No_Bool (R_Ty, Dim));

               L_First_E : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Left_Arr, Attr => Attribute_First, Dim => I),
                    To   => Base_Ty);
               L_Last_E  : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Left_Arr, Attr => Attribute_Last, Dim => I),
                    To   => Base_Ty);
               R_First_E : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Right_Arr, Attr => Attribute_First, Dim => I),
                    To   => Base_Ty);
               R_Last_E  : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Right_Arr, Attr => Attribute_Last, Dim => I),
                    To   => Base_Ty);
            begin
               Result :=
                 New_And_Pred
                   (Conjuncts =>
                      (1 => Result,
                       2 =>
                         New_Length_Equality
                           (L_First_E,
                            L_Last_E,
                            R_First_E,
                            R_Last_E,
                            Base_Ty)));
            end;
         end if;
      end loop;

      return +Result;
   end New_Length_Equality;

   function New_Length_Equality
     (Left_Arr : W_Term_Id; Right : Entity_Id; Dim : Positive) return W_Pred_Id
   is
      L_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (+Left_Arr));
      Is_Static : constant Boolean :=
        Has_Static_Array_Type (L_Ty) and then Has_Static_Array_Type (Right);
      Result    : W_Pred_Id := True_Pred;

   begin
      for I in 1 .. Dim loop

         --  Do not issue checks for statically matching lengths

         if not Is_Static
           or else Static_Array_Length (Retysp (L_Ty), I)
                   /= Static_Array_Length (Retysp (Right), I)
         then
            declare
               Base_Ty : constant W_Type_Id :=
                 Nth_Index_Rep_Type_No_Bool (L_Ty, Dim);
               pragma
                 Assert (Base_Ty = Nth_Index_Rep_Type_No_Bool (Right, Dim));

               L_First_E : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Left_Arr, Attr => Attribute_First, Dim => I),
                    To   => Base_Ty);
               L_Last_E  : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Expr => Left_Arr, Attr => Attribute_Last, Dim => I),
                    To   => Base_Ty);
               R_First_E : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Domain => EW_Term,
                         Ty     => Right,
                         Attr   => Attribute_First,
                         Dim    => I),
                    To   => Base_Ty);
               R_Last_E  : constant W_Term_Id :=
                 Insert_Simple_Conversion
                   (Expr =>
                      Get_Array_Attr
                        (Domain => EW_Term,
                         Ty     => Right,
                         Attr   => Attribute_Last,
                         Dim    => I),
                    To   => Base_Ty);
            begin
               Result :=
                 New_And_Pred
                   (Conjuncts =>
                      (1 => Result,
                       2 =>
                         New_Length_Equality
                           (L_First_E,
                            L_Last_E,
                            R_First_E,
                            R_Last_E,
                            Base_Ty)));
            end;
         end if;
      end loop;

      return +Result;
   end New_Length_Equality;

   -----------------------
   -- New_Logic_Eq_Call --
   -----------------------

   function New_Logic_Eq_Call
     (Left, Right : W_Term_Id; Domain : EW_Domain) return W_Expr_Id
   is
      Typ : constant W_Type_Id := Get_Type (+Left);
      E   : constant Entity_Id := Get_Ada_Node (+Typ);
      P   : constant W_Pred_Id :=
        New_Call
          (Name => E_Symb (E, WNE_Array_Logic_Eq),
           Args => (1 => +Left, 2 => +Right));
   begin
      return Boolean_Expr_Of_Pred (P, Domain);
   end New_Logic_Eq_Call;

   --------------------------------
   -- New_Move_Tree_Array_Access --
   --------------------------------

   function New_Move_Tree_Array_Access
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id is
   begin
      return
        New_Call
          (Name   => E_Symb (Ty, WNE_Move_Tree_Array_Get),
           Domain => Domain,
           Args   => Name & Index);
   end New_Move_Tree_Array_Access;

   --------------------------------
   -- New_Move_Tree_Array_Update --
   --------------------------------

   function New_Move_Tree_Array_Update
     (Name  : W_Prog_Id;
      Index : W_Expr_Array;
      Value : W_Prog_Id;
      Ty    : Entity_Id) return W_Prog_Id is
   begin
      return
        New_Call
          (Name => E_Symb (Ty, WNE_Move_Tree_Array_Set),
           Args => +Name & Index & W_Expr_Id'(+Value));
   end New_Move_Tree_Array_Update;

   -------------------------------------
   --  New_Move_Tree_Element_Equality --
   -------------------------------------

   function New_Move_Tree_Element_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Index     : W_Expr_Array;
      Ty        : Entity_Id) return W_Pred_Id
   is
      Left   : constant W_Expr_Id :=
        New_Move_Tree_Array_Access
          (Name => Left_Arr, Index => Index, Ty => Ty, Domain => EW_Term);
      Right  : constant W_Expr_Id :=
        New_Move_Tree_Array_Access
          (Name => Right_Arr, Index => Index, Ty => Ty, Domain => EW_Term);
      Result : constant W_Pred_Id :=
        +New_Comparison
           (Domain => EW_Pred, Symbol => Why_Eq, Left => Left, Right => Right);
   begin
      return Result;
   end New_Move_Tree_Element_Equality;

   ------------------------
   -- New_Singleton_Call --
   ------------------------

   function New_Singleton_Call
     (Domain : EW_Domain; Elt : W_Expr_Id; Pos : W_Expr_Id; Typ : W_Type_Id)
      return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
      E            : constant Entity_Id := Get_Ada_Node (+Typ);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => Get_Array_Theory_1 (E, Relaxed_Init).Singleton,
           Args   => (1 => Elt, 2 => Pos),
           Typ    => EW_Split (E, Relaxed_Init => Relaxed_Init));
   end New_Singleton_Call;

   --------------------
   -- New_Slice_Call --
   --------------------

   function New_Slice_Call
     (Domain : EW_Domain;
      Arr    : W_Expr_Id;
      Typ    : W_Type_Id;
      Low    : W_Expr_Id;
      High   : W_Expr_Id) return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
      E            : constant Entity_Id := Get_Ada_Node (+Typ);
   begin
      return
        New_Call
          (Domain => Domain,
           Name   => Get_Array_Theory (E, Relaxed_Init).Slice,
           Args   => (1 => Arr, 2 => Low, 3 => High),
           Typ    => EW_Split (E, Relaxed_Init => Relaxed_Init));
   end New_Slice_Call;

   function New_Slice_Call
     (Domain : EW_Domain; Arr : W_Expr_Id; Typ : W_Type_Id) return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
      E            : constant Entity_Id := Get_Ada_Node (+Typ);
      Dim          : constant Positive := Positive (Number_Dimensions (E));
      Args         : W_Expr_Array (1 .. Dim * 2 + 1);
      Arg_Ind      : Positive := 1;
      Expr         : constant W_Expr_Id := New_Temp_For_Expr (Arr);
      R            : W_Expr_Id;
   begin
      Add_Array_Arg (Domain, Args, Expr, Arg_Ind);
      Args (1) :=
        New_Call
          (Domain => Domain,
           Name   => Get_Array_Theory (E, Relaxed_Init).Slice,
           Args   => Args,
           Typ    => EW_Split (E, Relaxed_Init => Relaxed_Init));
      if Is_Static_Array_Type (Retysp (E)) then
         R :=
           New_Label
             (Domain => Domain,
              Labels => Symbol_Sets.Empty_Set,
              Def    => Args (1),
              Typ    => Typ);
      else
         R :=
           Array_Convert_From_Base
             (Domain       => Domain,
              Args         => Args,
              Ty           => E,
              Relaxed_Init => Relaxed_Init);
      end if;
      return Binding_For_Temp (Domain => Domain, Tmp => Expr, Context => R);
   end New_Slice_Call;

   ------------------------------------
   -- New_Validity_Tree_Array_Access --
   ------------------------------------

   function New_Validity_Tree_Array_Access
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id is
   begin
      return
        New_Call
          (Name   => E_Symb (Ty, WNE_Validity_Tree_Get),
           Domain => Domain,
           Args   => Name & Index,
           Typ    => Get_Validity_Tree_Type (Component_Type (Retysp (Ty))));
   end New_Validity_Tree_Array_Access;

   -----------------------------
   -- New_Validity_Tree_Slide --
   -----------------------------

   function New_Validity_Tree_Slide
     (Tree   : W_Expr_Id;
      Expr   : W_Expr_Id;
      To     : W_Type_Id;
      Domain : EW_Domain;
      Params : Transformation_Params) return W_Expr_Id
   is
      To_Ty   : constant Entity_Id := Get_Ada_Node (+To);
      Dim     : constant Positive := Positive (Number_Dimensions (To_Ty));
      Firsts  : W_Expr_Array (1 .. Dim * 2);
      Arg_Ind : Positive := 1;

   begin
      for I in 1 .. Dim loop
         Add_Attr_Arg (Domain, Firsts, Expr, Attribute_First, I, Arg_Ind);
         if Is_Constrained (To_Ty)
           or else Is_Fixed_Lower_Bound_Index_Subtype
                     (Nth_Index_Type (To_Ty, I))
         then
            Add_Attr_Arg
              (Domain, Firsts, To_Ty, Attribute_First, I, Arg_Ind, Params);
         else
            Add_Attr_Arg (Domain, Firsts, Expr, Attribute_First, I, Arg_Ind);
         end if;
      end loop;

      return
        New_Call
          (Domain => Domain,
           Name   => E_Symb (To_Ty, WNE_Validity_Tree_Slide),
           Args   => Tree & Firsts,
           Typ    => Get_Type (Tree));
   end New_Validity_Tree_Slide;

   ------------------------------------
   -- New_Validity_Tree_Array_Update --
   ------------------------------------

   function New_Validity_Tree_Array_Update
     (Name   : W_Expr_Id;
      Index  : W_Expr_Array;
      Value  : W_Expr_Id;
      Ty     : Entity_Id;
      Domain : EW_Domain) return W_Expr_Id is
   begin
      return
        New_Call
          (Name   => E_Symb (Ty, WNE_Validity_Tree_Set),
           Args   => +Name & Index & W_Expr_Id'(+Value),
           Typ    => Get_Type (+Name),
           Domain => Domain);
   end New_Validity_Tree_Array_Update;

   --------------------------
   -- New_Well_Formed_Pred --
   --------------------------

   function New_Well_Formed_Pred (Arr : W_Term_Id) return W_Pred_Id is
      Typ          : constant W_Type_Id := Get_Type (+Arr);
      Relaxed_Init : constant Boolean := Is_Init_Wrapper_Type (Typ);
      E            : constant Entity_Id := Get_Ada_Node (+Typ);
   begin
      return
        New_Call
          (Name => E_Symb (E, WNE_Array_Well_Formed, Relaxed_Init),
           Args => (1 => +Arr));
   end New_Well_Formed_Pred;

   -----------------------------------
   -- Prepare_Indexes_Substitutions --
   -----------------------------------

   function Prepare_Indexes_Substitutions
     (Th : Theory_UC; Typ : Entity_Id; Prefix : String)
      return W_Clone_Substitution_Array
   is
      WTyp       : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Base_Type (Typ));
      One_Id     : constant W_Identifier_Id :=
        New_Identifier (Name => "index_" & Prefix & "_one");
      Prefix_Mod : constant W_Module_Id :=
        New_Module (File => No_Symbol, Name => NID (Prefix));
   begin
      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => One_Id,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Binders     => (1 .. 0 => <>),
            Def         =>
              (if Is_Modular_Integer_Type (Typ)
                 and then not Has_No_Bitwise_Operations_Annotation (Typ)
               then New_Modular_Constant (Value => Uint_1, Typ => WTyp)
               else New_Integer_Constant (Value => Uint_1)),
            Return_Type => WTyp));

      --  ??? after Johannes refacto of names use this mecanism to print the
      --  new operators instead of NIDs.

      return
        (1 =>
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Name (Module => Prefix_Mod, Symb => NID ("t")),
              Image     => Get_Name (WTyp)),
         2 =>
           New_Clone_Substitution
             (Kind      => EW_Predicate,
              Orig_Name => New_Name (Module => Prefix_Mod, Symb => NID ("le")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).Ule
                   else Int_Infix_Le)),
         3 =>
           New_Clone_Substitution
             (Kind      => EW_Predicate,
              Orig_Name => New_Name (Module => Prefix_Mod, Symb => NID ("lt")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).Ult
                   else Int_Infix_Lt)),
         4 =>
           New_Clone_Substitution
             (Kind      => EW_Predicate,
              Orig_Name => New_Name (Module => Prefix_Mod, Symb => NID ("gt")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).Ugt
                   else Int_Infix_Gt)),
         5 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name =>
                New_Name (Module => Prefix_Mod, Symb => NID ("add")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).Add
                   else Int_Infix_Add)),
         6 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name =>
                New_Name (Module => Prefix_Mod, Symb => NID ("sub")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).Sub
                   else Int_Infix_Subtr)),
         7 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name =>
                New_Name (Module => Prefix_Mod, Symb => NID ("one")),
              Image     =>
                Get_Name
                  (if Is_Modular_Integer_Type (Typ)
                     and then not Has_No_Bitwise_Operations_Annotation (Typ)
                   then MF_BVs (WTyp).One
                   else One_Id)));
   end Prepare_Indexes_Substitutions;

   --------------------------------------------------
   -- Prepare_Standard_Array_Logical_Substitutions --
   --------------------------------------------------

   function Prepare_Standard_Array_Logical_Substitutions
     (Th : Theory_UC; Und_Ent : Entity_Id; Symbols : M_Array_Type)
      return W_Clone_Substitution_Array
   is ((1 =>
          New_Clone_Substitution
            (Kind      => EW_Type_Subst,
             Orig_Name => New_Name (Symb => NID ("map")),
             Image     => Get_Name (Symbols.Ty)),
        2 =>
          New_Clone_Substitution
            (Kind      => EW_Function,
             Orig_Name => New_Name (Symb => NID ("get")),
             Image     => Get_Name (Symbols.Get)))
       & Prepare_Indexes_Substitutions
           (Th, Etype (First_Index (Und_Ent)), "Index"));

   -------------------------------------------------
   -- Prepare_Subtype_Array_Logical_Substitutions --
   -------------------------------------------------

   function Prepare_Subtype_Array_Logical_Substitutions
     (Th : Theory_UC; Und_Ent : Entity_Id; Symbols : M_Array_Type)
      return W_Clone_Substitution_Array
   is (Prepare_Standard_Array_Logical_Substitutions (Th, Und_Ent, Symbols)
       & (1 =>
            New_Clone_Substitution
              (Kind      => EW_Type_Subst,
               Orig_Name => To_Name (WNE_Array_Component_Type),
               Image     => Get_Name (Symbols.Comp_Ty)),
          2 =>
            New_Clone_Substitution
              (Kind      => EW_Function,
               Orig_Name => New_Name (Symb => NID ("to_int")),
               Image     =>
                 Get_Name
                   (Conversion_Name
                      (From => +EW_Abstract (Component_Type (Und_Ent)),
                       To   => +EW_Int_Type))),
          3 =>
            New_Clone_Substitution
              (Kind      => EW_Function,
               Orig_Name => New_Name (Symb => NID ("of_int")),
               Image     =>
                 Get_Name
                   (Conversion_Name
                      (From => +EW_Int_Type,
                       To   => +EW_Abstract (Component_Type (Und_Ent)))))));

end Why.Gen.Arrays;
