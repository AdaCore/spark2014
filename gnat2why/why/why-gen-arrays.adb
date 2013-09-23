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

with Atree;               use Atree;
with Einfo;               use Einfo;
with Sem_Eval;            use Sem_Eval;
with Sinfo;               use Sinfo;
with Stand;               use Stand;
with Uintp;               use Uintp;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;
with Gnat2Why.Types;      use Gnat2Why.Types;

with VC_Kinds;            use VC_Kinds;

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Arrays is

   procedure Declare_Constrained (Theory         : W_Theory_Declaration_Id;
                                  Why3_Type_Name : W_Identifier_Id;
                                  Und_Ent        : Entity_Id);

   procedure Declare_Unconstrained (Theory         : W_Theory_Declaration_Id;
                                    Why3_Type_Name : W_Identifier_Id;
                                    Und_Ent        : Entity_Id);

   --  The following two procedures take an array [Args] and an index [Arg_Ind]
   --  as in-out parameters. They fill the array with a number of parameters,
   --  starting from the initial value of [Arg_Ind], and set the final value
   --  of [Arg_Ind] to the index after the last written value.

   procedure Add_Map_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Ty      : Entity_Id;
      Arg_Ind : in out Positive);
   --  Add an argument just for the "map" of the array. For constrained arrays,
   --  this is the identity, for unconstrained arrays, this corresponds to the
   --  selection of the corresponding field.

   procedure Add_Attr_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive);
   --  Add an argument for the corresponding attribute of the array. See alse
   --  [Get_Array_Attr].

   function Build_Length_Expr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Ty     : Entity_Id;
      Dim    : Positive) return W_Expr_Id;
   --  Given a type and an array expression, build the length expression for
   --  this array.

   -----------------
   -- Add_Map_Arg --
   -----------------

   procedure Add_Map_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Ty      : Entity_Id;
      Arg_Ind : in out Positive)
   is
      Ty_Name : constant String := Full_Name (Ty);
   begin
      if Is_Constrained (Ty) then
         Args (Arg_Ind) := Expr;
      else
         Args (Arg_Ind) :=
           New_Call
             (Domain => Domain,
              Name   =>
                Prefix (Ada_Node => Ty,
                        S        => Ty_Name,
                        W        => WNE_To_Array),
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
      Ty      : Entity_Id;
      Attr    : Attribute_Id;
      Dim     : Positive;
      Arg_Ind : in out Positive)
   is
   begin
      Args (Arg_Ind) := Get_Array_Attr (Domain, Expr, Ty, Attr, Dim);
      Arg_Ind := Arg_Ind + 1;
   end Add_Attr_Arg;

   -------------------
   -- Add_Array_Arg --
   -------------------

   procedure Add_Array_Arg
     (Domain  : EW_Domain;
      Args    : in out W_Expr_Array;
      Expr    : W_Expr_Id;
      Ty      : Entity_Id;
      Arg_Ind : in out Positive)
   is
      Dim     : constant Positive := Positive (Number_Dimensions (Ty));
   begin
      Add_Map_Arg (Domain, Args, Expr, Ty, Arg_Ind);
      for I in 1 .. Dim loop
         Add_Attr_Arg (Domain, Args, Expr, Ty, Attribute_First, I, Arg_Ind);
         Add_Attr_Arg (Domain, Args, Expr, Ty, Attribute_Last, I, Arg_Ind);
      end loop;
   end Add_Array_Arg;

   -----------------------
   -- Build_Length_Expr --
   -----------------------

   function Build_Length_Expr
     (Domain : EW_Domain;
      First, Last : W_Expr_Id) return W_Expr_Id
   is
      Cond : constant W_Expr_Id :=
        New_Relation
          (Domain  => Domain,
           Op_Type => EW_Int,
           Op      => EW_Le,
           Left    => +First,
           Right   => +Last);
      Len : constant W_Expr_Id :=
        New_Binary_Op
          (Op      => EW_Add,
           Op_Type => EW_Int,
           Left    =>
             New_Binary_Op
               (Op      => EW_Substract,
                Op_Type => EW_Int,
                Left    => Last,
                Right   => First),
           Right   => New_Integer_Constant (Value => Uint_1));
   begin
      return
        New_Conditional
          (Domain    => Domain,
           Condition => Cond,
           Then_Part => Len,
           Else_Part => New_Integer_Constant (Value => Uint_0));
   end Build_Length_Expr;

   function Build_Length_Expr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Ty     : Entity_Id;
      Dim    : Positive) return W_Expr_Id is
   begin
      return
        Build_Length_Expr
          (Domain,
           Get_Array_Attr (Domain, Expr, Ty, Attribute_First, Dim),
           Get_Array_Attr (Domain, Expr, Ty, Attribute_Last, Dim));
   end Build_Length_Expr;

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
      Int_Type  : constant W_Type_Id := +EW_Int_Type;
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
                  Why.Atree.Builders.New_Function_Decl
                    (Domain => EW_Term,
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
            New_Type_Decl
              (Why3_Type_Name,
               Alias =>
                 +New_Named_Type (Name => New_Identifier (Name => "__t"))));
   end Declare_Constrained;

   ---------------------------
   -- Declare_Unconstrained --
   ---------------------------

   procedure Declare_Unconstrained (Theory         : W_Theory_Declaration_Id;
                                    Why3_Type_Name : W_Identifier_Id;
                                    Und_Ent        : Entity_Id)
   is
      Dimension : constant Pos := Number_Dimensions (Und_Ent);
      Int_Type    : constant W_Type_Id := +EW_Int_Type;
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
            B_Type : constant W_Type_Id :=
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
            New_Type_Decl
              (Why3_Type_Name,
               Alias =>
                 +New_Named_Type (Name => New_Identifier (Name => "__t"))));
      if Und_Ent = Standard_String then
         declare
            Dummy_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "x");
            Image_Ty    : constant W_Type_Id :=
              +New_Named_Type (Name => New_Identifier (Name => "__image"));
            Str_Typ     : constant W_Type_Id :=
              +New_Named_Type (Name => Why3_Type_Name);
         begin
            Emit (Theory,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => New_Identifier (Name => "to_string"),
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                          Ada_Node => Empty,
                          Mutable  => False,
                          B_Ent    => null,
                          B_Name   => Dummy_Ident,
                          B_Type   => Image_Ty)),
                     Return_Type => Str_Typ));
            Emit (Theory,
                  Why.Gen.Binders.New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => New_Identifier (Name => "from_string"),
                     Binders     =>
                       (1 =>
                          Binder_Type'(
                          Ada_Node => Empty,
                          Mutable  => False,
                          B_Ent    => null,
                          B_Name   => Dummy_Ident,
                          B_Type   => Str_Typ)),
                     Return_Type => Image_Ty));
         end;
      end if;
   end Declare_Unconstrained;

   --------------------
   -- Get_Array_Attr --
   --------------------

   function Get_Array_Attr
     (Domain : EW_Domain;
      Expr   : W_Expr_Id;
      Ty     : Entity_Id;
      Attr   : Attribute_Id;
      Dim    : Positive) return W_Expr_Id
   is
      Ty_Name : constant String := Full_Name (Ty);
   begin
      if Is_Constrained (Ty) then
         return New_Attribute_Expr (Nth_Index_Type (Ty, Dim), Attr);
      else
         return
           New_Call
             (Domain => Domain,
              Name   =>
                Prefix
                  (Ada_Node => Ty,
                   P        => Ty_Name,
                   N        =>
                     Append_Num
                       (To_String
                          (Attr_To_Why_Name (Attr)),
                        Dim)),
              Args   => (1 => Expr));
      end if;
   end Get_Array_Attr;

   -----------------------------
   -- Insert_Array_Conversion --
   -----------------------------

   function Insert_Array_Conversion
     (Domain        : EW_Domain;
      Ada_Node      : Node_Id := Empty;
      Expr          : W_Expr_Id;
      To            : W_Type_Id;
      From          : W_Type_Id;
      Range_Check   : Node_Id := Empty) return W_Expr_Id
   is
      To_Ent    : constant Entity_Id := Get_Ada_Node (+To);
      From_Ent  : constant Entity_Id := Get_Ada_Node (+From);
      Dim       : constant Positive := Positive (Number_Dimensions (To_Ent));

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean;
      --  Check whether a conversion between those types requires sliding.

      function Insert_Length_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id;

      function Insert_Array_Range_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id;

      ------------------------------
      -- Insert_Array_Range_Check --
      ------------------------------

      function Insert_Array_Range_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id
      is
         Check   : W_Pred_Id;
         Args    : W_Expr_Array (1 .. 2 * Dim);
         Arg_Ind : Positive := 1;
      begin
         for I in 1 .. Dim loop
            Add_Attr_Arg
              (EW_Prog, Args, Expr, From_Ent, Attribute_First, I, Arg_Ind);
            Add_Attr_Arg
              (EW_Prog, Args, Expr, From_Ent, Attribute_Last, I, Arg_Ind);
         end loop;
         Check :=
           New_Call (Name   =>
                       Prefix (Ada_Node => To_Ent,
                               P        => Full_Name (To_Ent),
                               N        => "range_check"),
                     Args   => Args);
         return New_Located_Assert (Ada_Node, Check, VC_Range_Check);
      end Insert_Array_Range_Check;

      -------------------------
      -- Insert_Length_Check --
      -------------------------

      function Insert_Length_Check
        (Expr             : W_Expr_Id;
         From_Ent, To_Ent : Entity_Id) return W_Prog_Id
      is
         Check : W_Pred_Id := True_Pred;
      begin
         for I in 1 .. Dim loop
            declare
               Input_Length    : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, Expr, From_Ent, I);
               Expected_Length : constant W_Expr_Id :=
                 Build_Length_Expr (Domain, Why_Empty, To_Ent, I);
            begin
               Check :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Check,
                    Right  =>
                      New_Relation
                        (Domain  => Domain,
                         Op_Type => EW_Int,
                         Op      => EW_Eq,
                         Left    => +Input_Length,
                         Right   => +Expected_Length));
            end;
         end loop;
         return New_Located_Assert (Ada_Node, Check, VC_Length_Check);
      end Insert_Length_Check;

      -----------------
      -- Needs_Slide --
      -----------------

      function Needs_Slide (From_Ent, To_Ent : Entity_Id) return Boolean is
      begin
         --  Sliding is needed when we convert to a constrained type and the
         --  'First of the From type is not known to be equal to the 'First
         --  of the "To" type.

         --  Sliding is only necessary when converting to a constrained array

         if not Is_Constrained (To_Ent) then
            return False;
         end if;

         --  When the "To" is constrained, sliding is always necessary when
         --  converting from an unconstrained array

         if not Is_Constrained (From_Ent) then
            return True;
         end if;

         --  Here we have two constrained types, and we check if the 'First (I)
         --  of both types differ for some dimension I

         for I in 1 .. Dim loop
            declare
               Low_From : constant Node_Id :=
                 Get_Low_Bound (Nth_Index_Type (From_Ent, Dim));
               Low_To : constant Node_Id :=
                 Get_Low_Bound (Nth_Index_Type (To_Ent, Dim));
            begin
               if not Is_Static_Expression (Low_From) or else
                 not Is_Static_Expression (Low_To) or else
                 Expr_Value (Low_From) /= Expr_Value (Low_To) then
                  return True;
               end if;
            end;
         end loop;

         --  We statically know that the "first" are actually equal, no sliding
         --  needed

         return False;
      end Needs_Slide;

      Needs_Tmp   : Boolean := False;
      Sliding     : constant Boolean := Needs_Slide (From_Ent, To_Ent);
      Tmp_Var     : W_Identifier_Id;
      Arr_Expr    : W_Expr_Id;
      T           : W_Expr_Id;
      Arg_Ind     : Positive := 1;

      --  Beginning of processing for Insert_Array_Conversion

   begin

      if To_Ent = From_Ent then

         --  No range check needed

         return Expr;
      end if;

      --  We need a temp whenever there is a sliding, or when the "from" is
      --  unconstrained, and only when the expression is not a variable already

      Needs_Tmp :=
        Get_Kind (+Expr) in W_Identifier | W_Deref and then
        (Sliding or else not Is_Constrained (From_Ent));

      if Needs_Tmp then
         Tmp_Var := New_Temp_Identifier;
         Arr_Expr := +Tmp_Var;
      else
         Arr_Expr := Expr;
      end if;

      --  ??? do not forget range checks

      if Is_Constrained (To_Ent) then
         if Sliding then
            declare
               Args    : W_Expr_Array (1 .. 1 + 2 * Dim);
            begin
               Add_Map_Arg (Domain, Args, Arr_Expr, From_Ent, Arg_Ind);
               for I in 1 .. Dim loop
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr, From_Ent,
                     Attribute_First, Dim, Arg_Ind);
                  Add_Attr_Arg
                    (Domain, Args, Arr_Expr, To_Ent,
                     Attribute_First, Dim, Arg_Ind);
               end loop;
               T := New_Call
                 (Domain => Domain,
                  Name   =>
                    Prefix (P => To_String (Ada_Array_Name (Int (Dim))),
                            N => "slide"),
                  Args   => Args);
            end;
         elsif not Is_Constrained (From_Ent) then
               T :=
                 New_Call
                   (Domain => Domain,
                    Name   =>
                      Prefix (Ada_Node => From_Ent,
                              S        => Full_Name (From_Ent),
                              W        => WNE_To_Array),
                    Args => (1 => Arr_Expr));
         else
            T := Arr_Expr;
         end if;
      else
         declare
            Args     : W_Expr_Array (1 .. 2 * Dim + 1);
            Arg_Ind  : Positive := 1;
         begin
            Add_Array_Arg (Domain, Args, Arr_Expr, From_Ent, Arg_Ind);
            T :=
              New_Call
                (Domain => Domain,
                 Name   =>
                   Prefix (Ada_Node => To_Ent,
                           S        => Full_Name (To_Ent),
                           W        => WNE_Of_Array),
                 Args => Args);
         end;
      end if;

      if Range_Check /= Empty then
         declare
            Check_Type : Entity_Id;
            Check_Kind : Range_Check_Kind;
         begin
            Get_Range_Check_Info (Range_Check, Check_Type, Check_Kind);
            if Check_Kind = RCK_Length then
               T := +Sequence
                 (Insert_Length_Check (Arr_Expr, From_Ent, Check_Type),
                  +T);
            else
               pragma Assert (Check_Kind = RCK_Range);
               T := +Sequence
                 (Insert_Array_Range_Check (Arr_Expr, From_Ent, Check_Type),
                 +T);
            end if;
         end;
      end if;

      if Needs_Tmp then
         T :=
           New_Binding
             (Domain  => Domain,
              Name    => Tmp_Var,
              Def     => +Expr,
              Context => T);
      end if;
      return T;
   end Insert_Array_Conversion;

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
      Name      : constant W_Identifier_Id :=
        Prefix (Ada_Node => Ty_Entity,
                S => To_String (Ada_Array_Name (Dimension)),
                W => WNE_Array_Access);
      Elts     : constant W_Expr_Id :=
        (if Is_Constrained (Ty_Entity) then Ar
         else Array_Convert_To_Base (Ty_Entity, Domain, Ar));
   begin
      return
        New_Call
        (Ada_Node => Ada_Node,
         Name     => Name,
         Domain   => Domain,
         Args     => (1 => Elts) & Index);
   end New_Array_Access;

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
      Elmt_Type  : constant W_Type_Id := EW_Abstract (Comp_Type);
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
   begin
      if Is_Constrained (Ty_Entity) then
         return
           New_Call
             (Ada_Node => Ada_Node,
              Domain   => Domain,
              Name     => Name,
              Args     => (1 => +Ar) & Index & (1 => +Value));
      else
         declare
            Args      : constant W_Expr_Array :=
              (1 => New_Call
                 (Domain => Domain,
                  Name   =>
                    Prefix (Ada_Node => Ty_Entity,
                            S        => Full_Name (Ty_Entity),
                            W        => WNE_To_Array),
                  Args   => (1 => +Ar)))
              & Index & (1 => +Value);
            Array_Upd : constant W_Expr_Id :=
              New_Call
                (Ada_Node => Ada_Node,
                 Domain   => Domain,
                 Name     => Name,
                 Args     => Args);
         begin
            return
              New_Record_Update
                (Name    => Ar,
                 Updates =>
                   (1 =>
                          New_Field_Association
                      (Domain => Domain,
                       Field  => Prefix (Ada_Node => Ty_Entity,
                                         S        => Full_Name (Ty_Entity),
                                         W        => WNE_Array_Elts),
                       Value  => Array_Upd)));
         end;
      end if;
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

end Why.Gen.Arrays;
