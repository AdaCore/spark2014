------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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
with Common_Containers;     use Common_Containers;
with GNAT.Source_Info;
with Gnat2Why.Types;        use Gnat2Why.Types;
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with Namet;                 use Namet;
with Sinput;                use Sinput;
with SPARK_Atree;           use SPARK_Atree;
with SPARK_Util;            use SPARK_Util;
with Stand;                 use Stand;
with String_Utils;          use String_Utils;
with Uintp;                 use Uintp;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Conversions;       use Why.Conversions;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Init;          use Why.Gen.Init;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Images;            use Why.Images;
with Why.Inter;             use Why.Inter;
with Why.Types;             use Why.Types;

package body Why.Gen.Arrays is

   procedure Create_Rep_Array_Theory
     (File    : W_Section_Id;
      E       : Entity_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type);
   --  Create an Array theory
   --  @param File the current why file
   --  @param E the entity of type array
   --  @param Module the module in which the theory should be created
   --  @param Symbols the symbols to declared in this theory

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

   function Get_Comparison_Theory_Name (Name : Symbol) return Symbol is
     (NID (Img (Name) & To_String (WNE_Array_Comparison_Suffix)));
   --  @param Name name of an array representative theory
   --  @return The name of the theory for the comparison operators on these
   --          arrays.

   function Get_Concat_Theory_Name (Name : Symbol) return Symbol is
     (NID (Img (Name) & To_String (WNE_Array_Concatenation_Suffix)));
   --  @param Name name of an array representative theory
   --  @return The name of the theory for the concatenation operators on these
   --          arrays.

   function Get_Logical_Op_Theory_Name (Name : Symbol) return Symbol is
     (NID (Img (Name) & To_String (WNE_Array_Logical_Op_Suffix)));
   --  @param Name name of an array representative theory
   --  @return The name of the theory for the logical operators on these
   --          arrays.

   function New_Length_Equality
     (L_First_E : W_Expr_Id;
      L_Last_E  : W_Expr_Id;
      R_First_E : W_Expr_Id;
      R_Last_E  : W_Expr_Id;
      Base_Ty   : W_Type_Id) return W_Pred_Id;
   --  @param L_First_E first bound of the left array
   --  @param L_Last_E last bound of the left array
   --  @param R_First_E first bound of the right array
   --  @param R_Last_E last bound of the right array
   --  @param Base_Ty type of the bound expressions
   --  @return and expression stating that left and right have the same length
   --      avoiding the wraparound semantics on bitvectors.

   function Prepare_Indexes_Substitutions
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
      Und_Ent : Entity_Id;
      Symbols : M_Array_Type)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @param Symbols the symbols for the array theory.
   --  @return An array of substitutions for cloning the module
   --          Standard_Array_Logical_Ax.

   function Prepare_Subtype_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id;
      Symbols : M_Array_Type)
      return W_Clone_Substitution_Array;
   --  @param Und_Ent Entity of the array type.
   --  @param Symbols the symbols for the array theory.
   --  @return An array of substitutions for cloning the module
   --          Subtype_Array_Logical_Ax.

   procedure Declare_Equality_Function
     (E       : Entity_Id;
      Section : W_Section_Id;
      Symbols : M_Array_Type);
   --  @param E Entity of an array type.
   --  @param Symbols the symbols for the array theory.
   --  Declare the predefined equality for E

   procedure Declare_Concatenation_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type);
   --  @param E Entity of the one dimensional array type
   --  @param File The section in which the declaration should be added
   --  @param Module The module for these declarations
   --  @param Symbols the symbols for the array theory
   --  Clone module for concatenation functions (see M_Array_1_Type)

   procedure Declare_Logical_Operation_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type);
   --  @param E Entity of the one dimensional array type of Booleans
   --  @param File The section in which the declaration should be added
   --  @param Module The module for these declarations
   --  @param Symbols the symbols for the array theory.
   --  Clone module for logical operators (see M_Array_1_Bool_Op_Type)

   procedure Declare_Comparison_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type);
   --  @param E Entity of the one dimensional array type of discrete values
   --  @param File The section in which the declaration should be added
   --  @param Module The module for these declarations
   --  @param Symbols the symbols for the array theory
   --  Clone module for comparison functions (see M_Array_Comp_Type)

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
              Args   => (1 => Expr),
              Typ    => EW_Split (Ty));
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
      Arg_Ind : in out Positive;
      Params  : Transformation_Params := Body_Params)
   is
   begin
      Args (Arg_Ind) :=
        Insert_Conversion_To_Rep_No_Bool
          (Domain,
           Get_Array_Attr (Domain, Ty, Attr, Dim, Params));
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
      Dim  : constant Positive  := Positive (Number_Dimensions (Ty));
   begin
      Add_Map_Arg (Domain, Args, Expr, Arg_Ind);
      for I in 1 .. Dim loop
         Add_Attr_Arg (Domain, Args, Expr, Attribute_First, I, Arg_Ind);
         Add_Attr_Arg (Domain, Args, Expr, Attribute_Last,  I, Arg_Ind);
      end loop;
   end Add_Array_Arg;

   ----------------
   -- Append_Num --
   ----------------

   function Append_Num (S : String; Count : Positive) return String is
     (if Count = 1 then S else S & "_" & Image (Count, 1));

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

   function Array_Type_Is_Clone (E : Entity_Id) return Boolean is
     (not Is_Static_Array_Type (Retysp (E))
      and then Retysp (Etype (E)) /= Retysp (E));

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
            Cond      : constant W_Expr_Id :=
              New_Call
                (Domain => Domain,
                 Name   => MF_BVs (Typ).Ule,
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
      Indexes    : W_Expr_Array (1 .. Dim);
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
                                  Mutable  => False,
                                  Labels   => <>);
         Indexes (I) := +Tmp;
         Range_Expr := +New_And_Expr
           (Left   => +Range_Expr,
            Right  => New_Array_Range_Expr (+Tmp, +Expr, EW_Pred, I),
            Domain => EW_Pred);
         Next_Index (Index);
         I := I + 1;
      end loop;

      pragma Assert (I = Indexes'Last + 1);

      --  Call Build_Predicate_For_Comp on the array components.

      T_Comp :=
        +Build_Predicate_For_Comp
        (C_Expr => +New_Array_Access (Empty, +Expr, Indexes, EW_Term),
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

   ----------------------------------------------
   -- Create_Array_Conversion_Theory_If_Needed --
   ----------------------------------------------

   procedure Create_Array_Conversion_Theory_If_Needed
     (Current_File : W_Section_Id;
      From         : Entity_Id;
      To           : Entity_Id)
   is
      use Name_Id_Name_Id_Conversion_Name_Map;

      File       : constant W_Section_Id := WF_Pure;
      From_Name  : constant Symbol := Get_Array_Theory_Name (From);
      To_Name    : constant Symbol := Get_Array_Theory_Name (To);
      From_Symb  : constant M_Array_Type := M_Arrays.Element (From_Name);
      To_Symb    : constant M_Array_Type := M_Arrays.Element (To_Name);
      Module     : constant W_Module_Id :=
        New_Module (File => No_Symbol,
                    Name => Img (From_Name) & "__to__" & Img (To_Name));
      Convert_Id : constant W_Identifier_Id :=
        New_Identifier (Name      => "convert",
                        Module    => Module,
                        Typ       => To_Symb.Ty);
      A_Binder   : constant Binder_Type :=
        (Ada_Node => Empty,
         B_Name   => New_Identifier (Name => "a", Typ => From_Symb.Ty),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Labels   => <>);
      B_Binder   : constant Binder_Type :=
        (Ada_Node => Empty,
         B_Name   => New_Identifier (Name => "b", Typ => To_Symb.Ty),
         B_Ent    => Null_Entity_Name,
         Mutable  => False,
         Labels   => <>);

      C         : Cursor;
      Not_Found : Boolean;

      Save_Theory : W_Theory_Declaration_Id;
      --  Use this variable to temporarily store current theory

   begin
      --  Search for From_Name in M_Arrays_Conversion and initialize its value
      --  to Empty_Map if it is not found.

      M_Arrays_Conversion.Insert
        (Key      => From_Name,
         Position => C,
         Inserted => Not_Found);

      --  If there is a mapping for From_Name in M_Arrays_Conversion and it
      --  contains To_Name, then there is nothing to do.

      if not Not_Found and then M_Arrays_Conversion (C).Contains (To_Name) then
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
           "Module for array conversion from type "
         & """" & Get_Name_String (Chars (From)) & """"
         & (if Sloc (From) > 0 then
              " defined at " & Build_Location_String (Sloc (From))
           else "")
         & " to type "
         & """" & Get_Name_String (Chars (To)) & """"
         & (if Sloc (To) > 0 then
              " defined at " & Build_Location_String (Sloc (To))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an abstract conversion function from From to To

      Emit
        (File,
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
         T_Comp    : W_Expr_Id;
         Tmp       : W_Identifier_Id;
         T         : W_Pred_Id := True_Pred;

      begin
         while Present (Index) loop
            Tmp := New_Temp_Identifier
              (Typ => Base_Why_Type_No_Bool (Index));
            Indexes (I) := Binder_Type'(Ada_Node => Empty,
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
            From_Comp : constant Entity_Id := Retysp (Component_Type (From));
            To_Comp   : constant Entity_Id := Retysp (Component_Type (To));
            A_Comp    : W_Expr_Id := New_Init_Wrapper_Value_Access
              (Ada_Node => Empty,
               E        => From_Comp,
               Name     => New_Call
                 (Domain  => EW_Term,
                  Name    => From_Symb.Get,
                  Binders => A_Binder & Indexes,
                  Typ     => EW_Init_Wrapper (From_Comp, EW_Abstract)),
               Domain   => EW_Term);
            B_Comp    : W_Expr_Id := New_Init_Wrapper_Value_Access
              (Ada_Node => Empty,
               E        => To_Comp,
               Name     => New_Call
                 (Domain  => EW_Term,
                  Name    => To_Symb.Get,
                  Binders => B_Binder & Indexes,
                  Typ     => EW_Init_Wrapper (To_Comp, EW_Abstract)),
               Domain   => EW_Term);

         begin
            --  If components are arrays, go to split form

            if Is_Array_Type (From_Comp) then
               if not Has_Static_Array_Type (From_Comp) then
                  A_Comp := Array_Convert_To_Base (EW_Term, A_Comp);
               end if;

               if not Has_Static_Array_Type (To_Comp) then
                  B_Comp := Array_Convert_To_Base (EW_Term, B_Comp);
               end if;

            --  Otherwise, use base type

            else
               declare
                  BT : constant W_Type_Id := Base_Why_Type (From_Comp);
               begin
                  A_Comp := Insert_Simple_Conversion
                   (Domain         => EW_Term,
                    Expr           => A_Comp,
                    To             => BT,
                    Force_No_Slide => True);
                  B_Comp := Insert_Simple_Conversion
                   (Domain         => EW_Term,
                    Expr           => B_Comp,
                    To             => BT,
                    Force_No_Slide => True);
               end;
            end if;

            T_Comp :=
              New_Comparison
                (Symbol => Why_Eq,
                 Left   => A_Comp,
                 Right  => B_Comp,
                 Domain => EW_Pred);
         end;

         T := New_Universal_Quantif
           (Binders => Indexes,
            Pred    => +T_Comp);

         T := +New_Typed_Binding
           (Domain  => EW_Pred,
            Name    => B_Binder.B_Name,
            Def     => +Call_Expr,
            Context => +T);

         Emit
           (File,
            New_Guarded_Axiom
              (Name    => NID ("convert__def"),
               Binders => (1 => A_Binder),
               Def     => T));
      end;

      Close_Theory (File, Kind => Definition_Theory);

      --  Restore the current theory

      if File = Current_File then
         Why_Sections (File).Cur_Theory := Save_Theory;
      end if;

      M_Arrays_Conversion (C).Insert (To_Name, Convert_Id);
   end Create_Array_Conversion_Theory_If_Needed;

   -----------------------------
   -- Create_Rep_Array_Theory --
   -----------------------------

   procedure Create_Rep_Array_Theory
     (File    : W_Section_Id;
      E       : Entity_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type)
   is
      Typ : constant Entity_Id := Retysp (Etype (E));

      Dim : constant Positive := Positive (Number_Dimensions (Typ));

      Subst : W_Clone_Substitution_Array (1 .. Dim * 7 + 1);
      --  ??? why 7

   begin
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

            Subst (I * 7 + 1 .. I * 7 + 7) := Prepare_Indexes_Substitutions
              (File,
               Retysp (Etype (Index)),
               "I" & Image (I + 1, 1));

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

      Emit (File,
            New_Type_Decl (Name  => To_Name (WNE_Array_Component_Type),
                           Alias => EW_Init_Wrapper
                             (Component_Type (Typ), EW_Abstract)));

      Emit (File,
            New_Clone_Declaration
              (Theory_Kind   => EW_Theory,
               Clone_Kind    => EW_Export,
               Origin        => Array_Modules (Dim),
               As_Name       => No_Symbol,
               Substitutions => Subst));

      Declare_Equality_Function (Typ, File, Symbols);

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
      Name    : constant Symbol := Get_Array_Theory_Name (E);
      Module  : constant W_Module_Id := New_Module (File => No_Symbol,
                                                    Name => Img (Name));
      Symbols : constant M_Array_Type := Init_Array_Module (Module);

   begin
      if M_Arrays.Contains (Key => Name) then
         return;
      end if;

      --  If Name was inserted it means that the theory is not present:
      --  let's create it.

      if not Register_Only then
         Create_Rep_Array_Theory (File, E, Module, Symbols);
      end if;

      M_Arrays.Include (Key      => Name,
                        New_Item => Symbols);

      --  For arrays of dimension 1, we may need to clone additional modules
      --  containing definition for concatenation, the comparison function (if
      --  the component type is discrete) or of boolean operators (if the
      --  component type is boolean).

      if Number_Dimensions (Retysp (Etype (E))) = 1 then
         declare
            Array_1_Module : constant W_Module_Id :=
              New_Module (File => No_Symbol,
                          Name =>
                            Img (Get_Concat_Theory_Name (Name)));
         begin
            if not Register_Only then
               Declare_Concatenation_Symbols
                 (E, File, Array_1_Module, Symbols);
            end if;

            M_Arrays_1.Include (Key      => Name,
                                New_Item =>
                                  Init_Array_1_Module (Array_1_Module));
         end;

         --  For arrays of boolean types of dimension 1 we need to define the
         --  logical operators.

         if Has_Boolean_Type (Component_Type (Retysp (Etype (E)))) then
            declare
               Bool_Op_Module : constant W_Module_Id :=
                 New_Module (File => No_Symbol,
                             Name => Img (Get_Logical_Op_Theory_Name (Name)));
            begin
               if not Register_Only then
                  Declare_Logical_Operation_Symbols
                    (E, File, Bool_Op_Module, Symbols);
               end if;

               M_Arrays_1_Bool_Op.Include
                 (Key      => Name,
                  New_Item => Init_Array_1_Bool_Op_Module (Bool_Op_Module));
            end;
         end if;

         --  For arrays of discrete types of dimension 1 we need to define the
         --  comparison operators.

         if Has_Discrete_Type (Component_Type (Retysp (Etype (E)))) then
            declare
               Comp_Module : constant W_Module_Id :=
                 New_Module (File => No_Symbol,
                             Name => Img (Get_Comparison_Theory_Name (Name)));
            begin
               if not Register_Only then
                  Declare_Comparison_Symbols
                    (E, File, Comp_Module, Symbols);
               end if;

               M_Arrays_1_Comp.Include
                 (Key      => Name,
                  New_Item => Init_Array_1_Comp_Module (Comp_Module));
            end;
         end if;
      end if;
   end Create_Rep_Array_Theory_If_Needed;

   -----------------------
   -- Declare_Ada_Array --
   -----------------------

   procedure Declare_Ada_Array
     (File : W_Section_Id;
      E    : Entity_Id)
   is
      Why_Name : constant W_Name_Id := To_Why_Type (E, Local => True);
   begin
      if Array_Type_Is_Clone (E) then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and then return.

         declare
            Clone : constant Entity_Id := Array_Type_Cloned_Subtype (E);
         begin
            Add_With_Clause (File, E_Module (Clone), EW_Export);

            --  If the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (File,
                     New_Type_Decl
                       (Name  => Why_Name,
                        Alias =>
                          +New_Named_Type
                          (Name =>
                               To_Why_Type (Clone, Local => True))));
            end if;
         end;
      elsif Is_Static_Array_Type (E) then
         Declare_Constrained (File, E);
      else
         Declare_Unconstrained (File, Why_Name, E);
      end if;
   end Declare_Ada_Array;

   -------------------------------------------
   -- Declare_Additional_Symbols_For_String --
   -------------------------------------------

   procedure Declare_Additional_Symbols_For_String (Section : W_Section_Id) is
      Dummy_Ident       : constant W_Identifier_Id :=
        New_Identifier (Name => "x", Typ => M_Main.String_Image_Type);
      Size_Ident        : constant W_Identifier_Id :=
        New_Identifier (Name => "s", Typ => EW_Int_Type);
      To_String_Binders : constant Binder_Array :=
        (1 => Binder_Type'(Ada_Node => Empty,
                           Mutable  => False,
                           B_Ent    => Null_Entity_Name,
                           B_Name   => Dummy_Ident,
                           Labels   => <>),
         2 => Binder_Type'(Ada_Node => Empty,
                           Mutable  => False,
                           B_Ent    => Null_Entity_Name,
                           B_Name   => Size_Ident,
                           Labels   => <>));
      Str_Typ           : constant W_Type_Id := EW_Abstract (Standard_String);
      Dummy_Ident2      : constant W_Identifier_Id :=
        New_Identifier (Name => "x", Typ => Str_Typ);

   begin
      Add_With_Clause (Section, Int_Module, EW_Clone_Default);
      Add_With_Clause (Section, E_Module (Standard_String), EW_Clone_Default);

      --  Declare To_String and Of_String to convert between _image and string

      Emit (Section,
            Why.Gen.Binders.New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (To_String_Id),
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Binders     => To_String_Binders,
               Return_Type => Str_Typ));
      Emit (Section,
            Why.Gen.Binders.New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (Of_String_Id),
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Binders     =>
                 (1 =>
                      Binder_Type'(
                    Ada_Node => Empty,
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
         Call_Expr   : constant W_Expr_Id :=
           New_Call (Domain => EW_Term,
                     Name   => To_Local (To_String_Id),
                     Args   => (1 => +Dummy_Ident,
                                2 => +Size_Ident),
                     Typ    => Str_Typ);
         Guard       : constant W_Pred_Id :=
           +New_Comparison
             (Symbol => Int_Infix_Ge,
              Left   => +Size_Ident,
              Right  => New_Integer_Constant (Value => Uint_0),
              Domain => EW_Pred);
      begin
         Emit (Section,
               New_Guarded_Axiom
                 (Name     => NID ("to_string__first"),
                  Binders  => To_String_Binders,
                  Triggers => New_Triggers
                    (Triggers =>
                         (1 => New_Trigger (Terms => (1 => Call_Expr)))),
                  Def      => +New_Comparison
                    (Symbol => Why_Eq,
                     Left   =>
                       Get_Array_Attr (Domain => EW_Term,
                                       Expr   => Call_Expr,
                                       Attr   => Attribute_First,
                                       Dim    => 1),
                     Right  =>
                       New_Discrete_Constant (Value => Uint_1,
                                              Typ   => EW_Int_Type),
                     Domain => EW_Pred)));
         Emit (Section,
               New_Guarded_Axiom
                 (Name     => NID ("to_string__length"),
                  Binders  => To_String_Binders,
                  Triggers => New_Triggers
                    (Triggers =>
                         (1 => New_Trigger (Terms => (1 => Call_Expr)))),
                  Pre      => Guard,
                  Def      => +New_Comparison
                    (Symbol => Int_Infix_Le,
                     Left   =>
                       Get_Array_Attr (Domain => EW_Term,
                                       Expr   => Call_Expr,
                                       Attr   => Attribute_Length,
                                       Dim    => 1),
                     Right  => +Size_Ident,
                     Domain => EW_Pred)));
      end;
   end Declare_Additional_Symbols_For_String;

   --------------------------------
   -- Declare_Comparison_Symbols --
   --------------------------------

   procedure Declare_Comparison_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type)
   is
      Fst_Idx       : constant Node_Id :=
        First_Index (if Ekind (E) = E_String_Literal_Subtype
                     then Retysp (Etype (E))
                     else E);
      Component_Typ : constant Entity_Id := Component_Type (E);
      Base          : constant W_Type_Id :=
        Base_Why_Type_No_Bool (Component_Typ);
      To_Rep_Name   : W_Identifier_Id :=
        Conversion_Name
          (From => EW_Abstract (Component_Typ),
           To   => Base);

   begin
      Open_Theory
        (File, Module,
         Comment =>
           "Module for axiomatizing comparison for the array theory"
         & " associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  If components have wrappers, we cannot use To_Rep symbol as is.
      --  Generate a new To_Rep symbol for this case.

      if Needs_Init_Wrapper_Type (Component_Typ) then
         declare
            A_Ident  : constant W_Identifier_Id :=
              New_Identifier (Name => "a",
                              Typ  => EW_Init_Wrapper
                                (Component_Typ, EW_Abstract));
            A_Binder : constant Binder_Array :=
              (1 => (B_Name => A_Ident,
                     others => <>));
         begin
            Emit (File,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (To_Rep_Name),
                     Binders     => A_Binder,
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => Base,
                     Def         => New_Call
                       (Domain  => EW_Term,
                        Name    => To_Rep_Name,
                        Args    =>
                          (1 => New_Init_Wrapper_Value_Access
                               (Ada_Node => Empty,
                                E        => Component_Typ,
                                Name     => +A_Ident,
                                Domain   => EW_Term)),
                        Typ     => Base)));

            To_Rep_Name := To_Local (To_Rep_Name);
         end;
      end if;

      declare
         Sbst          : constant W_Clone_Substitution_Array :=
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
          &
           Prepare_Indexes_Substitutions
           (File, Base_Type (Etype (Fst_Idx)), "Index")
          &
           (1 =>
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
         if Has_Modular_Integer_Type (Component_Typ) then
            Emit (File,
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
                     As_Name       => No_Symbol,
                     Substitutions => Sbst));
         else
            Emit (File,
                  New_Clone_Declaration
                    (Theory_Kind   => EW_Module,
                     Clone_Kind    => EW_Export,
                     Origin        => Array_Int_Rep_Comparison_Ax,
                     As_Name       => No_Symbol,
                     Substitutions => Sbst));
         end if;
      end;

      Close_Theory (File, Kind => Definition_Theory);
   end Declare_Comparison_Symbols;

   -----------------------------------
   -- Declare_Concatenation_Symbols --
   -----------------------------------

   procedure Declare_Concatenation_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type)
   is
      Fst_Idx : constant Node_Id :=
        First_Index (if Ekind (E) = E_String_Literal_Subtype
                     then Retysp (Etype (E))
                     else E);

   begin
      Open_Theory
        (File, Module,
         Comment =>
           "Module for axiomatizing concatenation for the array theory"
         & " associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      declare
         Sbst : constant W_Clone_Substitution_Array :=
           (1 =>
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => To_Name (WNE_Array_Component_Type),
                 Image     => Get_Name (Symbols.Comp_Ty)),
            2 =>
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name (Symb => NID ("map")),
                 Image     => Get_Name (Symbols.Ty)))
         &
           Prepare_Indexes_Substitutions
           (File, Base_Type (Etype (Fst_Idx)), "Index")
         &
           (1 =>
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symb => NID ("get")),
                 Image     => Get_Name (Symbols.Get)));
      begin

         --  Clone concatenation module

         Emit (File,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        => Array_Concat_Axioms,
                  As_Name       => No_Symbol,
                  Substitutions => Sbst));

         Close_Theory (File, Kind => Definition_Theory);
      end;

   end Declare_Concatenation_Symbols;

   -------------------------------
   -- Declare_Equality_Function --
   -------------------------------

   procedure Declare_Equality_Function
     (E       : Entity_Id;
      Section : W_Section_Id;
      Symbols : M_Array_Type)
   is
      Map_Ty     : constant W_Type_Id :=
        New_Named_Type (Name => To_Local (Get_Name (Symbols.Ty)));
      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Map_Ty);
      B_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "b", Typ => Map_Ty);
      Dim        : constant Positive := Positive (Number_Dimensions (E));
      Idx_Vars   : Binder_Array (1 .. Dim);
      --  Binders for quantified index variables.
      --  idx1 idx2 ...

      Args_Lgth  : constant Natural := Dim * 2 + 1;
      Args       : Binder_Array (1 .. 2 * Args_Lgth);
      --  Binders for the parameters of the equality function.
      --  a a__first a__last a__first_2 ... b  b__first ...

      A_Indexes  : W_Expr_Array (1 .. Dim + 1);
      --  Expressions used to access an element in A.
      --  a idx1 idx2 ...

      B_Indexes  : W_Expr_Array (1 .. Dim + 1);
      --  Expressions used to access an element in B.
      --  b (b__first - a__first + idx1) ...

      Range_Cond : W_Pred_Id := True_Pred;
      --  The index variables are in range.
      --  a__first <= idx1 <= a__last /\ ...

      Length_Eq  : W_Pred_Id := True_Pred;
      --  The arrays have the same length.
      --  (if a__first <= a__last then a__last - a__first = b__last - b__first
      --   else b__first > b__last) /\ ...

      Index      : Node_Id := First_Index (E);
      I          : Positive := 1;

   begin
      --  Store a and b in Args

      Args (1) := Binder_Type'(Ada_Node => Empty,
                               B_Name   => A_Ident,
                               B_Ent    => Null_Entity_Name,
                               Mutable  => False,
                               Labels   => <>);
      Args (Args_Lgth + 1) := Binder_Type'(Ada_Node => Empty,
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
              Binder_Type'(Ada_Node => Empty,
                           B_Name   => Idx,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => False,
                           Labels   => <>);

            --  Store the first and last bounds of a and b in Args

            Args (2 * I) :=
              Binder_Type'(Ada_Node => Empty,
                           B_Name   => A_Fst,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => False,
                           Labels   => <>);
            Args (2 * I + 1) :=
              Binder_Type'(Ada_Node => Empty,
                           B_Name   => A_Lst,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => False,
                           Labels   => <>);
            Args (Args_Lgth + 2 * I) :=
              Binder_Type'(Ada_Node => Empty,
                           B_Name   => B_Fst,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => False,
                           Labels   => <>);
            Args (Args_Lgth + 2 * I + 1) :=
              Binder_Type'(Ada_Node => Empty,
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

            Range_Cond := +New_And_Expr
              (Left   => +Range_Cond,
               Right  => New_Range_Expr (Domain => EW_Pred,
                                         Low    => +A_Fst,
                                         High   => +A_Lst,
                                         Expr   => +Idx),
               Domain => EW_Pred);

            --  Compute the equality of lengths

            Length_Eq := +New_And_Expr
              (Left   => +Length_Eq,
               Right  =>
                 New_Conditional
                   (Domain      => EW_Pred,
                    Condition   => New_Comparison
                      (Symbol => (if Typ = EW_Int_Type
                                  then Int_Infix_Le
                                  elsif Why_Type_Is_BitVector (Typ)
                                  then MF_BVs (Typ).Ule
                                  else raise Program_Error),
                       Left   => +A_Fst,
                       Right  => +A_Lst,
                       Domain => EW_Pred),
                    Then_Part   => New_And_Expr
                      (Left   => New_Comparison
                      (Symbol => (if Typ = EW_Int_Type
                                  then Int_Infix_Le
                                  elsif Why_Type_Is_BitVector (Typ)
                                  then MF_BVs (Typ).Ule
                                  else raise Program_Error),
                       Left   => +B_Fst,
                       Right  => +B_Lst,
                       Domain => EW_Pred),
                       Right  => New_Comparison
                         (Symbol => Why_Eq,
                          Left   =>
                            New_Discrete_Substract (EW_Pred, +A_Lst, +A_Fst),
                          Right  =>
                            New_Discrete_Substract (EW_Pred, +B_Lst, +B_Fst),
                          Domain => EW_Pred),
                       Domain => EW_Pred),
                    Else_Part   => New_Comparison
                      (Symbol => (if Typ = EW_Int_Type
                                  then Int_Infix_Gt
                                  elsif Why_Type_Is_BitVector (Typ)
                                  then MF_BVs (Typ).Ugt
                                  else raise Program_Error),
                       Left   => +B_Fst,
                       Right  => +B_Lst,
                       Domain => EW_Pred),
                    Typ         => EW_Bool_Type),
               Domain => EW_Pred);

            Next_Index (Index);
            I := I + 1;
         end;
      end loop;

      --  If the type is limited, still declare an abstract placeholder for
      --  the equality function which will be used to clone the array theory.

      if Is_Limited_View (E) then

         Emit
           (Section,
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
            W_Ty     : constant W_Type_Id := EW_Init_Wrapper
              (C_Type, EW_Abstract);
            Get_Name : constant W_Identifier_Id := To_Local (Symbols.Get);
            Eq_Name  : constant W_Identifier_Id := To_Local (Symbols.Bool_Eq);
            Def      : W_Pred_Id :=
              +New_Ada_Equality
              (Typ    => C_Type,
               Domain => EW_Pred,
               Left   =>
                 New_Init_Wrapper_Value_Access
                   (Ada_Node => Empty,
                    E        => C_Type,
                    Name     => New_Call
                      (Empty, EW_Term, Get_Name, A_Indexes, W_Ty),
                    Domain   => EW_Term),
               Right  =>
                 New_Init_Wrapper_Value_Access
                   (Ada_Node => Empty,
                    E        => C_Type,
                    Name     => New_Call
                      (Empty, EW_Term, Get_Name, B_Indexes, W_Ty),
                    Domain   => EW_Term));
         begin

            Def := New_Conditional
              (Condition => +Range_Cond,
               Then_Part => +Def,
               Typ       => EW_Bool_Type);

            Def := New_Universal_Quantif
              (Binders => Idx_Vars,
               Pred    => +Def);

            Def := +New_And_Expr
              (Left   => +Length_Eq,
               Right  => +Def,
               Domain => EW_Pred);

            Emit
              (Section,
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
                 Args (Args_Lgth + 1 .. 2 * Args_Lgth)
                 & Args (1 .. Args_Lgth);
               Rev_Call : constant W_Expr_Id :=
                 New_Call (Empty, EW_Term, Eq_Name, Rev_Args, EW_Bool_Type);
            begin
               Emit
                 (Section,
                  New_Guarded_Axiom
                    (Name    => NID ("bool_eq_rev"),
                     Binders => Args,
                     Pre     => +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => Rev_Call,
                        Right  => +True_Term,
                        Domain => EW_Pred),
                     Def     => Def));
            end;
         end;
      end if;
   end Declare_Equality_Function;

   ---------------------------------------
   -- Declare_Logical_Operation_Symbols --
   ---------------------------------------

   procedure Declare_Logical_Operation_Symbols
     (E       : Entity_Id;
      File    : W_Section_Id;
      Module  : W_Module_Id;
      Symbols : M_Array_Type)
   is
      Arr_Symbs     : M_Array_Type := Symbols;
      Component_Typ : constant Entity_Id := Component_Type (E);

   begin
      Open_Theory
        (File, Module,
         Comment =>
           "Module for axiomatizing logical operations for the array theory"
         & " associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  If components have wrappers, we cannot use Get symbol as is.
      --  Generate a new Get symbol for this case.

      if Needs_Init_Wrapper_Type (Component_Typ) then
         declare
            A_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "a",
                              Typ  => Arr_Symbs.Ty);
            I_Ident : constant W_Identifier_Id :=
              New_Identifier
                (Name => "i",
                 Typ  => Base_Why_Type_No_Bool (Etype (First_Index (E))));
            Binders : constant Binder_Array :=
              (1 => (B_Name => A_Ident,
                     others => <>),
               2 => (B_Name => I_Ident,
                     others => <>));
         begin
            Emit (File,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (Arr_Symbs.Get),
                     Binders     => Binders,
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => EW_Abstract (Component_Typ),
                     Def         => New_Init_Wrapper_Value_Access
                       (Ada_Node    => Empty,
                        E           => Component_Typ,
                        Name        => New_Call
                          (Domain  => EW_Term,
                           Name    => Arr_Symbs.Get,
                           Args    => (1 => +A_Ident, 2 => +I_Ident),
                           Typ     => EW_Init_Wrapper
                             (Component_Typ, EW_Abstract)),
                        Domain      => EW_Term)));

            Arr_Symbs.Get := To_Local (Arr_Symbs.Get);
            Arr_Symbs.Comp_Ty := EW_Abstract (Component_Typ);
         end;
      end if;

      if Is_Standard_Boolean_Type (Component_Typ) then

         --  For Boolean, use the module Standard_Array_Logical_Op_Axioms

         Emit (File,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        => Standard_Array_Logical_Ax,
                  As_Name       => No_Symbol,
                  Substitutions =>
                    Prepare_Standard_Array_Logical_Substitutions
                      (File, E, Arr_Symbs)));
      else

         --  We clone a specific module Subtype_Array_Logical_Op_Axioms
         --  which needs an additional parameter to_int.

         Emit (File,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  Origin        => Subtype_Array_Logical_Ax,
                  As_Name       => No_Symbol,
                  Substitutions =>
                    Prepare_Subtype_Array_Logical_Substitutions
                      (File, E, Arr_Symbs)));
      end if;

      Close_Theory (File, Kind => Definition_Theory);
   end Declare_Logical_Operation_Symbols;

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
                    (Domain      => EW_Pterm,
                     Name        => New_Identifier (Attr_Name),
                     Binders     => (1 .. 0 => <>),
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => Typ,
                     Def         => New_Discrete_Constant
                       (Value => Value,
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
           Orig_Name => New_Name (Symb => NID ("map")),
           Image     => New_Name (Symb   => NID ("map"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Function,
           Orig_Name => New_Name (Symb => NID ("array_bool_eq")),
           Image     => New_Name (Symb   => NID ("bool_eq"),
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
                       Orig_Name =>
                         New_Name
                           (Symb => NID
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
               As_Name       => No_Symbol,
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
            New_Type_Decl (Name  => To_Name (WNE_Array_Component_Type),
                           Alias => EW_Abstract (Component_Type (Und_Ent))));

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => New_Name (Symb => NID ("map")),
           Image     => New_Name (Symb   => NID ("map"),
                                  Module => Array_Theory));
      Cursor := Cursor + 1;

      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Function,
           Orig_Name => New_Name (Symb => NID ("array_bool_eq")),
           Image     => New_Name (Symb   => NID ("bool_eq"),
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
                   (Symb => NID (Append_Num ("index_base_type", Dim_Count))),
                 Image     => Ident_Of_Ada_Type (B_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => New_Name
                   (Symb => NID (Append_Num ("index_rep_type", Dim_Count))),
                 Image     => Get_Name (R_Ty));
            Cursor := Cursor + 1;

            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name
                   (Symb => NID (Append_Num ("to_rep", Dim_Count))),
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
                          (Domain      => EW_Term,
                           Name        => Id_Id,
                           Binders     =>
                             (1 => (B_Name => X_Id, others => <>)),
                           Labels      => Symbol_Sets.Empty_Set,
                           Location    => No_Location,
                           Def         => +X_Id,
                           Return_Type => R_Ty));

                  Subst (Cursor) :=
                    New_Clone_Substitution
                      (Kind      => EW_Function,
                       Orig_Name => New_Name
                         (Symb => NID
                            (Append_Num ("rep_to_int", Dim_Count))),
                       Image     => Get_Name (Id_Id));
               end;
            else
               Subst (Cursor) :=
                 New_Clone_Substitution
                   (Kind      => EW_Function,
                    Orig_Name => New_Name
                      (Symb => NID (Append_Num ("rep_to_int", Dim_Count))),
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
                   (Symb => NID (Append_Num ("index_rep_le", Dim_Count))),
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
               As_Name       => No_Symbol,
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

   -------------------------------
   -- Get_Array_Conversion_Name --
   -------------------------------

   function Get_Array_Conversion_Name
     (From, To : Entity_Id) return W_Identifier_Id
   is
     (M_Arrays_Conversion (Get_Array_Theory_Name (From))
      (Get_Array_Theory_Name (To)));

   ----------------------
   -- Get_Array_Theory --
   ----------------------

   function Get_Array_Theory (E : Entity_Id) return M_Array_Type is
     (M_Arrays (Get_Array_Theory_Name (E)));

   ------------------------
   -- Get_Array_Theory_1 --
   ------------------------

   function Get_Array_Theory_1 (E : Entity_Id) return M_Array_1_Type is
     (M_Arrays_1 (Get_Array_Theory_Name (E)));

   -----------------------------
   -- Get_Array_Theory_1_Comp --
   -----------------------------

   function Get_Array_Theory_1_Comp (E : Entity_Id) return M_Array_1_Comp_Type
   is
     (M_Arrays_1_Comp (Get_Array_Theory_Name (E)));

   --------------------------------
   -- Get_Array_Theory_1_Bool_Op --
   --------------------------------

   function Get_Array_Theory_1_Bool_Op (E : Entity_Id)
                                        return M_Array_1_Bool_Op_Type is
     (M_Arrays_1_Bool_Op (Get_Array_Theory_Name (E)));

   ---------------------------
   -- Get_Array_Theory_Name --
   ---------------------------

   function Get_Array_Theory_Name (E : Entity_Id) return Symbol is
      Name      : Unbounded_String :=
        To_Unbounded_String (To_String (WNE_Array_Prefix));
      Ty        : constant Entity_Id := Retysp (E);
      Type_Name : Unbounded_String;
      Index     : Node_Id := First_Index (Ty);
      Dim       : constant Positive :=
        Positive (Number_Dimensions (Ty));
   begin
      if Ekind (Ty) = E_String_Literal_Subtype then
         return Get_Array_Theory_Name (Etype (Ty));
      end if;

      for I in 1 .. Dim loop
         if Has_Modular_Integer_Type (Etype (Index)) then
            Type_Name := To_Unbounded_String
              (To_String (WNE_Array_BV_Suffix)
               & Image (Integer (UI_To_Int
                 (Modular_Size (Etype (Index)))), 1));
         else
            Type_Name :=
              To_Unbounded_String (To_String (WNE_Array_Int_Suffix));
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

   ----------------------------
   -- Get_Entity_Of_Variable --
   ----------------------------

   function Get_Entity_Of_Variable (E : W_Expr_Id) return Entity_Id is
   begin
      pragma Assert (Get_Kind (+E) in W_Deref
                                    | W_Identifier
                                    | W_Statement_Sequence
                                    | W_Tagged
                                    | W_Label);

      case Get_Kind (+E) is
         when W_Identifier | W_Statement_Sequence =>
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

         when W_Label =>
            declare
               Expr : constant W_Expr_Id := Get_Def (W_Label_Id (E));
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
     (Ada_Node : Node_Id;
      Ar       : W_Expr_Id;
      Index    : W_Expr_Array;
      Domain   : EW_Domain) return W_Expr_Id
   is
      Why_Ty    : constant W_Type_Id := Get_Type (Ar);
      Ty_Entity : constant Entity_Id := Get_Ada_Node (+Why_Ty);
      Name      : constant W_Identifier_Id :=
        Get_Array_Theory (Ty_Entity).Get;
      Elts      : W_Expr_Id;
      Comp_Ty   : constant Entity_Id :=
        Retysp (Component_Type (Ty_Entity));

   begin
      if Is_Static_Array_Type (Ty_Entity) or else
        Get_Type_Kind (Why_Ty) = EW_Split
      then
         Elts := Ar;
      else
         Elts := Array_Convert_To_Base (Domain, Ar);
      end if;

      return New_Call
        (Ada_Node => Ada_Node,
         Name     => Name,
         Domain   => Domain,
         Args     => (1 => Elts) & Index,
         Typ      => EW_Init_Wrapper (Comp_Ty, EW_Abstract));
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
      Val       : constant W_Expr_Id :=
        Reconstruct_Init_Wrapper
          (Ada_Node => Ada_Node,
           Ty       => Retysp (Component_Type (Ty_Entity)),
           Value    => Value);
   begin
      if Is_Static_Array_Type (Ty_Entity)
        or else Get_Type_Kind (W_Ty) = EW_Split
      then
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
              (1 => New_Call
                 (Domain => Domain,
                  Name   => E_Symb (Ty_Entity, WNE_To_Array),
                  Args   => (1 => +Ar)))
              & Index & (1 => +Val);
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

   -------------------------
   -- New_Bounds_Equality --
   -------------------------

   function New_Bounds_Equality
     (Left_Arr     : W_Expr_Id;
      Right_Bounds : W_Expr_Array;
      Dim          : Positive;
      Domain       : EW_Domain := EW_Pred) return W_Expr_Id
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
                    Right  => Right_Bounds (2 * I - 1),
                    Domain => Domain),

                 --  <left_arr>.last__I = <right_arr>.last__I

                 3 => New_Comparison
                   (Symbol => Why_Eq,
                    Left   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    Right  => Right_Bounds (2 * I),
                    Domain => Domain)),
              Domain    => Domain);
      end loop;

      return +Result;
   end New_Bounds_Equality;

   function New_Bounds_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Dim       : Positive) return W_Pred_Id
   is
      Right_Bounds : W_Expr_Array (1 .. 2 * Dim);
      Count        : Positive := 1;
   begin
      for I in 1 .. Dim loop
         Add_Attr_Arg
           (EW_Term, Right_Bounds, Right_Arr, Attribute_First, I, Count);
         Add_Attr_Arg
           (EW_Term, Right_Bounds, Right_Arr, Attribute_Last,  I, Count);
      end loop;

      return +New_Bounds_Equality (Left_Arr, Right_Bounds, Dim);
   end New_Bounds_Equality;

   function New_Bounds_Equality
     (Left_Arr : W_Expr_Id;
      Right_Ty : Entity_Id;
      Domain   : EW_Domain := EW_Pred;
      Params   : Transformation_Params := Body_Params) return W_Expr_Id
   is
      Dim          : constant Positive :=
        Positive (Number_Dimensions (Right_Ty));
      Right_Bounds : W_Expr_Array (1 .. 2 * Dim);
      Count        : Positive := 1;
   begin
      for I in 1 .. Dim loop
         Add_Attr_Arg
           (EW_Term, Right_Bounds, Right_Ty,
            Attribute_First, I, Count, Params);
         Add_Attr_Arg
           (EW_Term, Right_Bounds, Right_Ty, Attribute_Last, I, Count, Params);
      end loop;

      return New_Bounds_Equality (Left_Arr, Right_Bounds, Dim, Domain);
   end New_Bounds_Equality;

   ---------------------
   -- New_Concat_Call --
   ---------------------

   function New_Concat_Call
     (Domain             : EW_Domain;
      Args               : W_Expr_Array;
      Typ                : W_Type_Id;
      Is_Component_Left  : Boolean;
      Is_Component_Right : Boolean) return W_Expr_Id is
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Get_Array_Theory_1 (Get_Ada_Node (+Typ)).Concat
              (Is_Component_Left, Is_Component_Right),
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
      Rep_Ty : constant Entity_Id := Retysp (Ty);
      Dim       : constant Positive := Positive (Number_Dimensions (Rep_Ty));
      Call_Args : W_Expr_Array (1 .. 4 * Dim);

   begin
      pragma Assert (Args'Length = 2 * Dim);
      for Count in 0 .. Dim - 1 loop
         declare
            W_Typ      : constant W_Type_Id :=
              Nth_Index_Rep_Type_No_Bool (E   => Rep_Ty,
                                          Dim => Count + 1);
            First_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Get_Array_Attr
                                          (Domain => Domain,
                                           Ty     => Rep_Ty,
                                           Attr   => Attribute_First,
                                           Dim    => Count + 1,
                                           Params => Params),
                                        To     => W_Typ);
            Last_Expr : constant W_Expr_Id :=
              Insert_Simple_Conversion (Domain => Domain,
                                        Expr   => Get_Array_Attr
                                          (Domain => Domain,
                                           Ty     => Rep_Ty,
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
          (Domain => EW_Pred,
           Symbol => Why_Eq,
           Left   => Left,
           Right  => Right);
   begin
      return Result;
   end New_Element_Equality;

   -------------------------
   -- New_Length_Equality --
   -------------------------

   function New_Length_Equality
     (L_First_E : W_Expr_Id;
      L_Last_E  : W_Expr_Id;
      R_First_E : W_Expr_Id;
      R_Last_E  : W_Expr_Id;
      Base_Ty   : W_Type_Id) return W_Pred_Id
   is
      Le_Op     : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type then Int_Infix_Le
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Ule
         else raise Program_Error);
      Lt_Op     : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type then Int_Infix_Lt
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Ult
         else raise Program_Error);
      Sub_Op    : constant W_Identifier_Id :=
        (if Base_Ty = EW_Int_Type then Int_Infix_Subtr
         elsif Why_Type_Is_BitVector (Base_Ty)
         then MF_BVs (Base_Ty).Sub
         else raise Program_Error);

   begin
        --  (if <left_arr>.first_I <= <left_arr>.last_I then
        --     <right_arr>.first_I <= <right_arr>.last_I
        --     /\ <left_arr>.last_I - <left_arr>.first_I =
        --        <right_arr>.last_I - <right_arr>.first_I
        --   else <right_arr>.last_I < <right_arr>.first_I)

      return New_Conditional
        (Condition => New_Call
           (Domain   => EW_Pred,
            Name     => Le_Op,
            Args     => (L_First_E, L_Last_E),
            Typ      => EW_Bool_Type),
         Then_Part => New_And_Then_Expr
           (Left   => New_Call
                (Domain   => EW_Pred,
                 Name     => Le_Op,
                 Args     => (R_First_E, R_Last_E),
                 Typ      => EW_Bool_Type),
            Right  => New_Comparison
              (Symbol => Why_Eq,
               Left   => New_Call
                 (Domain   => EW_Pred,
                  Name     => Sub_Op,
                  Args     => (L_Last_E, L_First_E),
                  Typ      => Base_Ty),
               Right  => New_Call
                 (Domain   => EW_Pred,
                  Name     => Sub_Op,
                  Args     => (R_Last_E, R_First_E),
                  Typ      => Base_Ty),
               Domain => EW_Pred),
            Domain => EW_Pred),
         Else_Part => New_Call
           (Domain => EW_Pred,
            Name   => Lt_Op,
            Args   => (R_Last_E, R_First_E),
            Typ    => Base_Ty),
         Typ       => EW_Bool_Type);
   end New_Length_Equality;

   function New_Length_Equality
     (Left_Arr  : W_Expr_Id;
      Right_Arr : W_Expr_Id;
      Dim       : Positive) return W_Pred_Id
   is
      L_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (Left_Arr));
      R_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (Right_Arr));
      Is_Static : constant Boolean := Has_Static_Array_Type (L_Ty)
        and then Has_Static_Array_Type (R_Ty);
      Result    : W_Expr_Id := +True_Pred;

   begin
      for I in 1 .. Dim loop

         --  Do not issue checks for statically matching lengths

         if not Is_Static
           or else Static_Array_Length (Retysp (L_Ty), I) /=
             Static_Array_Length (Retysp (R_Ty), I)
         then
            declare
               Base_Ty   : constant W_Type_Id :=
                Nth_Index_Rep_Type_No_Bool (L_Ty, Dim);
               pragma Assert
                 (Base_Ty = Nth_Index_Rep_Type_No_Bool (R_Ty, Dim));

               L_First_E : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    To     => Base_Ty);
               L_Last_E  : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    To     => Base_Ty);
               R_First_E : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Right_Arr,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    To     => Base_Ty);
               R_Last_E  : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Right_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    To     => Base_Ty);
            begin
               Result :=
                 New_And_Expr
                   (Conjuncts =>
                      (1 => Result,
                       2 => +New_Length_Equality
                         (L_First_E, L_Last_E, R_First_E, R_Last_E, Base_Ty)),
                    Domain    => EW_Pred);
            end;
         end if;
      end loop;

      return +Result;
   end New_Length_Equality;

   function New_Length_Equality
     (Left_Arr : W_Expr_Id;
      Right    : Entity_Id;
      Dim      : Positive) return W_Pred_Id
   is
      L_Ty      : constant Entity_Id := Get_Ada_Node (+Get_Type (Left_Arr));
      Is_Static : constant Boolean := Has_Static_Array_Type (L_Ty)
        and then Has_Static_Array_Type (Right);
      Result    : W_Expr_Id := +True_Pred;

   begin
      for I in 1 .. Dim loop

         --  Do not issue checks for statically matching lengths

         if not Is_Static
           or else Static_Array_Length (Retysp (L_Ty), I) /=
             Static_Array_Length (Retysp (Right), I)
         then
            declare
               Base_Ty   : constant W_Type_Id :=
                Nth_Index_Rep_Type_No_Bool (L_Ty, Dim);
               pragma Assert
                 (Base_Ty = Nth_Index_Rep_Type_No_Bool (Right, Dim));

               L_First_E : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    To     => Base_Ty);
               L_Last_E  : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Expr   => Left_Arr,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    To     => Base_Ty);
               R_First_E : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Ty     => Right,
                                              Attr   => Attribute_First,
                                              Dim    => I),
                    To     => Base_Ty);
               R_Last_E  : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => Get_Array_Attr (Domain => EW_Term,
                                              Ty     => Right,
                                              Attr   => Attribute_Last,
                                              Dim    => I),
                    To     => Base_Ty);
            begin
               Result :=
                 New_And_Expr
                   (Conjuncts =>
                      (1 => Result,
                       2 => +New_Length_Equality
                         (L_First_E, L_Last_E, R_First_E, R_Last_E, Base_Ty)),
                    Domain    => EW_Pred);
            end;
         end if;
      end loop;

      return +Result;
   end New_Length_Equality;

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
           Args   => (1 => Elt, 2 => Pos),
           Typ    => EW_Split (Typ));
   end New_Singleton_Call;

   -----------------------------------
   -- Prepare_Indexes_Substitutions --
   -----------------------------------

   function Prepare_Indexes_Substitutions
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
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
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
               Orig_Name => New_Name (Symb => NID (Prefix & ".t")),
               Image     => Get_Name (WTyp)),
              2 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".le")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ule
                    else
                      Int_Infix_Le)),
              3 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".lt")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ult
                    else
                      Int_Infix_Lt)),
              4 => New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".gt")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Ugt
                    else
                      Int_Infix_Gt)),
              5 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".add")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Add
                    else
                      Int_Infix_Add)),
              6 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".sub")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).Sub
                    else
                      Int_Infix_Subtr)),
              7 => New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => New_Name (Symb => NID (Prefix & ".one")),
                 Image     => Get_Name
                   (if Is_Modular_Integer_Type (Typ) then
                      MF_BVs (WTyp).One
                    else
                      One_Id)));
   end Prepare_Indexes_Substitutions;

   --------------------------------------------------
   -- Prepare_Standard_Array_Logical_Substitutions --
   --------------------------------------------------

   function Prepare_Standard_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id;
      Symbols : M_Array_Type)
      return W_Clone_Substitution_Array
   is
     ((1 =>
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
        (Section, Etype (First_Index (Und_Ent)), "Index",
         Declare_One => True));

   -------------------------------------------------
   -- Prepare_Subtype_Array_Logical_Substitutions --
   -------------------------------------------------

   function Prepare_Subtype_Array_Logical_Substitutions
     (Section : W_Section_Id;
      Und_Ent : Entity_Id;
      Symbols : M_Array_Type)
      return W_Clone_Substitution_Array
   is
     (Prepare_Standard_Array_Logical_Substitutions (Section, Und_Ent, Symbols)
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
                Get_Name (Conversion_Name
                            (From =>
                               +EW_Abstract (Component_Type (Und_Ent)),
                             To   => +EW_Int_Type))),
         3 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => New_Name (Symb => NID ("of_int")),
              Image     =>
                Get_Name (Conversion_Name
                            (From => +EW_Int_Type,
                             To   =>
                               +EW_Abstract (Component_Type (Und_Ent)))))));

end Why.Gen.Arrays;
