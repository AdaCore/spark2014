------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Atree;              use Atree;
with Einfo;              use Einfo;
with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with Stand;              use Stand;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;
with Gnat2Why.Types;     use Gnat2Why.Types;

with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Inter;          use Why.Inter;

package body Why.Gen.Arrays is

   procedure Declare_Constrained (Theory         : W_Theory_Declaration_Id;
                                  Why3_Type_Name : W_Identifier_Id;
                                  Und_Ent        : Entity_Id);

   procedure Declare_Unconstrained (Theory         : W_Theory_Declaration_Id;
                                    Why3_Type_Name : W_Identifier_Id;
                                    Und_Ent        : Entity_Id);

   -----------------------
   -- Declare_Ada_Array --
   -----------------------

   procedure Declare_Ada_Array
     (Theory         : W_Theory_Declaration_Id;
      Und_Ent        : Entity_Id)
   is
      Why_Name : constant W_Identifier_Id :=
        To_Why_Id (Und_Ent, Local => True);
   begin
      if Is_Constrained (Und_Ent) then
         Declare_Constrained (Theory, Why_Name, Und_Ent);
      else
         Declare_Unconstrained (Theory, Why_Name, Und_Ent);
      end if;
   end Declare_Ada_Array;

   -------------------------
   -- Declare_Constrained --
   -------------------------

   procedure Declare_Constrained (Theory         : W_Theory_Declaration_Id;
                                  Why3_Type_Name : W_Identifier_Id;
                                  Und_Ent        : Entity_Id)
   is
      Dimension : constant Pos := Number_Dimensions (Und_Ent);
      Int_Type  : constant W_Primitive_Type_Id :=
        New_Base_Type (Base_Type => EW_Int);
      Index     : Entity_Id := First_Index (Und_Ent);
      Subst     : W_Clone_Substitution_Array
        (1 .. Integer (Dimension * 2) + 1);
      Cursor    : Integer := 1;
      Clone_Id  : constant W_Identifier_Id :=
        Append_Num ("""ada__model"".Constr_Array", Positive (Dimension));

      procedure Declare_Attribute (Kind : Why_Name_Enum;
                                   Def  : Node_Id;
                                   Dim_Count : Positive);

      -----------------------
      -- Declare_Attribute --
      -----------------------

      procedure Declare_Attribute (Kind : Why_Name_Enum;
                                   Def  : Node_Id;
                                   Dim_Count : Positive)
      is
         Attr_Name : constant W_Identifier_Id := Append_Num (Kind, Dim_Count);
      begin
         if Present (Def) and then Is_Static_Expression (Def) then
            Emit (Theory,
                  New_Function_Def (Domain => EW_Term,
                                    Name   => Attr_Name,
                                    Binders => (1 .. 0 => <>),
                                    Return_Type => Int_Type,
                                    Def => New_Integer_Constant
                                      (Value => Expr_Value (Def))));
         else
            Emit (Theory,
                  New_Function_Decl (Domain => EW_Term,
                                     Name   => Attr_Name,
                                     Binders => (1 .. 0 => <>),
                                     Return_Type => Int_Type));
         end if;
         Subst (Cursor) :=
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => Attr_Name,
              Image     => Attr_Name);
         Cursor := Cursor + 1;
      end Declare_Attribute;

   begin
      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => New_Identifier (Name => "component_type"),
           Image     => Ident_Of_Ada_Type (Component_Type (Und_Ent)));
      Cursor := Cursor + 1;
      if Ekind (Und_Ent) in String_Kind then
         Declare_Attribute (WNE_Attr_First,
                            String_Literal_Low_Bound (Und_Ent),
                            1);
         Declare_Attribute (WNE_Attr_Last,
                            Empty,
                            1);
      else
         declare
            Count : Positive := 1;
         begin
            while Present (Index) loop
               declare
                  Rng   : constant Node_Id := Get_Range (Index);
               begin
                  Declare_Attribute (WNE_Attr_First,
                                     Low_Bound (Rng),
                                     Count);
                  Declare_Attribute (WNE_Attr_Last,
                                     High_Bound (Rng),
                                     Count);
                  Count := Count + 1;
                  Next_Index (Index);
               end;
            end loop;
         end;
      end if;
      Emit (Theory,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               Origin        => Clone_Id,
               Substitutions => Subst));
      Emit (Theory,
            New_Type
              (Why3_Type_Name,
               Alias =>
                 New_Abstract_Type (Name => New_Identifier (Name => "__t"))));
   end Declare_Constrained;

   ---------------------------
   -- Declare_Unconstrained --
   ---------------------------

   procedure Declare_Unconstrained (Theory         : W_Theory_Declaration_Id;
                                    Why3_Type_Name : W_Identifier_Id;
                                    Und_Ent        : Entity_Id)
   is
      Dimension : constant Pos := Number_Dimensions (Und_Ent);
      Int_Type    : constant W_Primitive_Type_Id :=
        New_Base_Type (Base_Type => EW_Int);
      Subst     : W_Clone_Substitution_Array
        (1 .. Integer (Dimension * 4) + 1);
      Cursor    : Integer := 1;
      Index     : Node_Id := First_Index (Und_Ent);
      Dim_Count : Integer := 1;
      Clone_Id  : constant W_Identifier_Id :=
        Append_Num ("""ada__model"".Unconstr_Array", Positive (Dimension));
   begin
      Subst (Cursor) :=
        New_Clone_Substitution
          (Kind      => EW_Type_Subst,
           Orig_Name => New_Identifier (Name => "component_type"),
           Image     => Ident_Of_Ada_Type (Component_Type (Und_Ent)));
      Cursor := Cursor + 1;
      while Present (Index) loop
         declare
            Ind_Ty : constant Entity_Id := Etype (Index);
            B_Ty   : constant Entity_Id := Base_Type (Ind_Ty);
            B_Type : constant W_Primitive_Type_Id :=
              +Type_Of_Node (B_Ty);
         begin
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Type_Subst,
                 Orig_Name => Append_Num ("base_type", Dim_Count),
                 Image     => Ident_Of_Ada_Type (B_Ty));
            Cursor := Cursor + 1;
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Function,
                 Orig_Name => Append_Num ("to_int", Dim_Count),
                 Image     => Conversion_Name (From => +B_Type,
                                               To => +Int_Type));
            Cursor := Cursor + 1;
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => Append_Num ("in_range_base", Dim_Count),
                 Image     => Range_Pred_Name (B_Ty));
            Cursor := Cursor + 1;
            Subst (Cursor) :=
              New_Clone_Substitution
                (Kind      => EW_Predicate,
                 Orig_Name => Append_Num ("in_range", Dim_Count),
                 Image     =>
                   Range_Pred_Name (Ind_Ty));
            Cursor := Cursor + 1;
         end;
         Dim_Count := Dim_Count + 1;
         Next_Index (Index);
      end loop;

      Emit (Theory,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               Origin        => Clone_Id,
               Substitutions => Subst));
      Emit (Theory,
            New_Type
              (Why3_Type_Name,
               Alias =>
                 New_Abstract_Type (Name => New_Identifier (Name => "__t"))));
      if Und_Ent = Standard_String then
         declare
            Dummy_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "x");
            Image_Ty    : constant W_Primitive_Type_Id :=
              New_Abstract_Type (Name => New_Identifier (Name => "__image"));
            Str_Typ     : constant W_Primitive_Type_Id :=
              New_Abstract_Type (Name => Why3_Type_Name);
         begin
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => New_Identifier (Name => "to_string"),
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                            Ada_Node => Empty,
                            Modifier => None,
                            B_Name   => Dummy_Ident,
                            B_Type   => Image_Ty)),
                     Return_Type => Str_Typ));
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => New_Identifier (Name => "from_string"),
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                            Ada_Node => Empty,
                            Modifier => None,
                            B_Name   => Dummy_Ident,
                            B_Type   => Str_Typ)),
                     Return_Type => Image_Ty));
         end;
      end if;
   end Declare_Unconstrained;

   ----------------------
   -- New_Array_Access --
   ----------------------

   function New_Array_Access
     (Ada_Node  : Node_Id;
      Ty_Entity : Entity_Id;
      Ar        : W_Expr_Id;
      Index     : W_Expr_Array;
      Domain    : EW_Domain;
      Dimension : Pos) return W_Expr_Id
   is
      Progs     : constant W_Expr_Array :=
        Index & (1 => Array_Convert_To_Base (Ty_Entity, Domain, Ar));
   begin
      return New_Simple_Array_Access
        (Ada_Node  => Ada_Node,
         Domain    => Domain,
         Dimension => Dimension,
         Args      => Progs);
   end New_Array_Access;

   --------------------
   -- New_Array_Attr --
   --------------------

   function New_Array_Attr
     (Attr      : Attribute_Id;
      Ty_Entity : Entity_Id;
      Ar        : W_Expr_Id;
      Domain    : EW_Domain;
      Dimension : Pos;
      Argument  : Uint) return W_Expr_Id
   is
      Name : constant W_Identifier_Id :=
        (if Present (Ty_Entity) then
         Prefix (Ada_Node => Ty_Entity,
                 S        => Full_Name (Ty_Entity),
                 W        => WNE_To_Array)
         else
         To_Ident (WNE_To_Array));
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Attr_To_Why_Name (A     => Attr,
                               Dim   => Dimension,
                               Count => Argument),
           Args   =>
             (1 =>
                New_Call
                  (Domain => Domain,
                   Name   => Name,
                   Args   => (1 => +Ar))));
   end New_Array_Attr;

   ---------------------------
   --  New_Element_Equality --
   ---------------------------

   function New_Element_Equality
     (Ada_Node   : Node_Id := Empty;
      Left_Arr   : W_Expr_Id;
      Left_Type  : Entity_Id;
      Right_Arr  : W_Expr_Id;
      Right_Type : Entity_Id;
      Index      : W_Expr_Array;
      Dimension  : Pos) return W_Pred_Id
   is
      Comp_Type  : constant Node_Id := Component_Type (Left_Type);
      Elmt_Type  : constant W_Base_Type_Id :=
        +Why_Logic_Type_Of_Ada_Type (Comp_Type);
      Left       : constant W_Expr_Id :=
        New_Array_Access
          (Ada_Node  => Ada_Node,
           Domain    => EW_Term,
           Ty_Entity => Left_Type,
           Ar        => Left_Arr,
           Index     => Index,
           Dimension => Dimension);
      Right      : constant W_Expr_Id :=
        New_Array_Access
          (Ada_Node  => Ada_Node,
           Domain    => EW_Term,
           Ty_Entity => Right_Type,
           Ar        => Right_Arr,
           Index     => Index,
           Dimension => Dimension);
      Result     : constant W_Pred_Id :=
        +New_Comparison
        (Domain    => EW_Pred,
         Cmp       => EW_Eq,
         Left      => Left,
         Right     => Right,
         Arg_Types => Elmt_Type);
   begin
      return Result;
   end New_Element_Equality;

   ----------------------
   -- New_Array_Update --
   ----------------------

   function New_Array_Update
     (Ada_Node  : Node_Id;
      Ty_Entity : Entity_Id;
      Ar        : W_Expr_Id;
      Index     : W_Expr_Array;
      Value     : W_Expr_Id;
      Domain    : EW_Domain;
      Dimension : Pos) return W_Expr_Id
   is
      Name      : constant W_Identifier_Id :=
        Prefix (S => To_String (Ada_Array_Name (Dimension)),
                W => WNE_Array_Update);
      Args      : constant W_Expr_Array :=
        Index & (1 => New_Call
                 (Domain => Domain,
                  Name   =>
                    Prefix (Ada_Node => Ty_Entity,
                            S        => Full_Name (Ty_Entity),
                            W        => WNE_To_Array),
                                     Args   => (1 => +Ar)),
                 2 => +Value);
      Array_Upd : constant W_Expr_Id :=
                    New_Call
                      (Ada_Node => Ada_Node,
                       Domain   => Domain,
                       Name     => Name,
                       Args     => Args);
   begin
      return
        New_Call
          (Name   =>
               Prefix (Ada_Node => Ty_Entity,
                       S        => Full_Name (Ty_Entity),
                       W        => WNE_Of_Array),
           Args   => (1 => Array_Upd),
           Domain => Domain);
   end New_Array_Update;

   -------------------------------
   -- New_Prepared_Array_Access --
   -------------------------------

   function Array_Convert_To_Base
     (Ty_Entity : Entity_Id;
      Domain    : EW_Domain;
      Ar        : W_Expr_Id) return W_Expr_Id
   is
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Prefix (Ada_Node => Ty_Entity,
                     S        => Full_Name (Ty_Entity),
                     W        => WNE_To_Array),
           Args   => (1 => +Ar));
   end Array_Convert_To_Base;

   -----------------------------
   -- New_Simple_Array_Access --
   -----------------------------

   function New_Simple_Array_Access
     (Ada_Node  : Node_Id;
      Domain    : EW_Domain;
      Dimension : Pos;
      Args      : W_Expr_Array) return W_Expr_Id
   is
      Name      : constant W_Identifier_Id :=
        Prefix (S => To_String (Ada_Array_Name (Dimension)),
                W => WNE_Array_Access);
   begin
      return
        New_Call
        (Ada_Node => Ada_Node,
         Name     => Name,
         Domain   => Domain,
         Args    => Args);
   end New_Simple_Array_Access;

   ---------------------------
   -- New_Simple_Array_Attr --
   ---------------------------

   function New_Simple_Array_Attr
     (Attr      : Attribute_Id;
      Ar        : W_Expr_Id;
      Domain    : EW_Domain;
      Dimension : Pos;
      Argument  : Uint) return W_Expr_Id is
   begin
      return
        New_Call
          (Domain => Domain,
           Name   =>
             Attr_To_Why_Name (A     => Attr,
                               Dim   => Dimension,
                               Count => Argument),
           Args => (1 => Ar));
   end New_Simple_Array_Attr;

end Why.Gen.Arrays;
