------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
      Dimension   : constant Pos := Number_Dimensions (Und_Ent);
      Array_Base  : constant Why_Name_Enum := Ada_Array_Name (Dimension);
      BT_Id       : constant W_Identifier_Id := Prefix (Array_Base, WNE_Type);
      Comp_Type   : constant W_Primitive_Type_Id :=
        Why_Logic_Type_Of_Ada_Type (Component_Type (Und_Ent));
      Ar_Type     : constant W_Primitive_Type_Id :=
                     New_Generic_Actual_Type_Chain
                       (Type_Chain => (1 => Comp_Type),
                        Name       => BT_Id);
      Name_Type   : constant W_Primitive_Type_Id :=
        New_Abstract_Type (Name => Why3_Type_Name);
      A_Ident     : constant W_Identifier_Id := New_Identifier (Name => "a");
      Ar_Binder : constant Binder_Type :=
                      (B_Name => A_Ident,
                       B_Type => Ar_Type,
                       others => <>);
      Int_Type    : constant W_Primitive_Type_Id :=
        New_Base_Type (Base_Type => EW_Int);
      Conv_From   : constant W_Identifier_Id := To_Ident (WNE_Of_Array);
      Conv_To     : constant W_Identifier_Id := To_Ident (WNE_To_Array);
      Index       : Entity_Id := First_Index (Und_Ent);

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
      begin
         if Present (Def) and then Is_Static_Expression (Def) then
            Emit (Theory,
                  New_Function_Def (Domain => EW_Term,
                                    Name   => Append_Num (Kind, Dim_Count),
                                    Binders => (1 .. 0 => <>),
                                    Return_Type => Int_Type,
                                    Def => New_Integer_Constant
                                      (Value => Expr_Value (Def))));
         else
            Emit (Theory,
                  New_Function_Decl (Domain => EW_Term,
                                     Name   => Append_Num (Kind, Dim_Count),
                                     Binders => (1 .. 0 => <>),
                                     Return_Type => Int_Type));
         end if;
      end Declare_Attribute;

      Rec_Binders : Binder_Array (1 .. Integer (Dimension) + 1);
   begin
      Rec_Binders (1) :=
        (B_Name => To_Ident (WNE_Array_Elts),
         B_Type =>
           New_Generic_Actual_Type_Chain
             (Type_Chain => (1 => Comp_Type),
              Name => Prefix (To_String (Array_Base), "map")),
        others => <>);
      for Count in 1 .. Integer (Dimension) loop
         Rec_Binders (Count + 1) :=
           (B_Name => Append_Num (WNE_Array_Offset, Count),
            B_Type => Int_Type,
            others => <>);
      end loop;

      Emit
        (Theory,
         New_Record_Definition
           (Name    => Why3_Type_Name,
            Binders => Rec_Binders));
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
      declare
         --  in the "to" conversion, we need a field for "elts", and for
         --  each dimension, fields for first, last, offset
         To_Aggr : W_Field_Association_Array
           (1 .. Integer (Dimension) * 3 + 1);
         --  in the "from" conversion, we need a field for "elts", and for
         --  each dimension, a field for "offset"
         From_Aggr : W_Field_Association_Array
           (1 .. Integer (Dimension) + 1);
      begin
         To_Aggr (1) :=
           New_Field_Association
             (Field => Prefix (Array_Base, WNE_Array_Elts),
              Domain => EW_Term,
              Value =>
                New_Record_Access
                  (Name => +A_Ident,
                   Field => To_Ident (WNE_Array_Elts)));
         From_Aggr (1) :=
           New_Field_Association
             (Field => To_Ident (WNE_Array_Elts),
              Domain => EW_Term,
              Value =>
                New_Record_Access
                  (Name => +A_Ident,
                   Field => Prefix (Array_Base, WNE_Array_Elts)));
         for Count in 1 .. Integer (Dimension) loop
            To_Aggr (3 * Count - 1) :=
              New_Field_Association
                (Field =>
                     Append_Num (Array_Base, WNE_Array_First_Field, Count),
                 Domain => EW_Term,
                 Value => +Append_Num (WNE_Attr_First, Count));
            To_Aggr (3 * Count) :=
              New_Field_Association
                (Field =>
                     Append_Num (Array_Base, WNE_Array_Last_Field, Count),
                 Domain => EW_Term,
                 Value => +Append_Num (WNE_Attr_Last, Count));
            To_Aggr (3 * Count + 1) :=
              New_Field_Association
                (Field => Append_Num (Array_Base, WNE_Array_Offset, Count),
                 Domain => EW_Term,
                 Value =>
                   New_Record_Access
                     (Name => +A_Ident,
                      Field => +Append_Num (WNE_Array_Offset, Count)));
            From_Aggr (Count + 1) :=
              New_Field_Association
                (Field => Append_Num (WNE_Array_Offset, Count),
                 Domain => EW_Term,
                 Value =>
                   New_Record_Access
                     (Name  => +A_Ident,
                      Field =>
                        Append_Num (Array_Base, WNE_Array_Offset, Count)));
         end loop;
         Emit
           (Theory,
            New_Function_Def
              (Domain      => EW_Term,
               Name        => Conv_To,
               Binders     =>
                 (1 => (B_Name => A_Ident,
                        B_Type => Name_Type,
                        others => <>)),
               Def         =>
                 New_Record_Aggregate (Associations => To_Aggr),
               Return_Type => Ar_Type));
         Emit
           (Theory,
            New_Function_Def
              (Domain      => EW_Term,
               Name        => Conv_From,
               Binders     => (1 => Ar_Binder),
               Return_Type => Name_Type,
               Def         =>
                 New_Record_Aggregate (Associations => From_Aggr)));
      end;
   end Declare_Constrained;

   ---------------------------
   -- Declare_Unconstrained --
   ---------------------------

   procedure Declare_Unconstrained (Theory         : W_Theory_Declaration_Id;
                                    Why3_Type_Name : W_Identifier_Id;
                                    Und_Ent        : Entity_Id)
   is
      Dimension : constant Pos := Number_Dimensions (Und_Ent);
      Array_Base  : constant Why_Name_Enum := Ada_Array_Name (Dimension);
      BT_Id       : constant W_Identifier_Id :=
        Prefix (Array_Base, WNE_Type);
      Comp_Type   : constant W_Primitive_Type_Id :=
        Why_Logic_Type_Of_Ada_Type (Component_Type (Und_Ent));
      Name_Type   : constant W_Primitive_Type_Id :=
        New_Abstract_Type (Name => Why3_Type_Name);
      Ar_Type     : constant W_Primitive_Type_Id :=
        New_Generic_Actual_Type_Chain
          (Type_Chain => (1 => Comp_Type),
           Name       => BT_Id);
      Conv_From   : constant W_Identifier_Id := To_Ident (WNE_Of_Array);
      Conv_To     : constant W_Identifier_Id := To_Ident (WNE_To_Array);
      A_Ident     : constant W_Identifier_Id := New_Identifier (Name => "a");
      Int_Type    : constant W_Primitive_Type_Id :=
        New_Base_Type (Base_Type => EW_Int);
      Ar_Binder   : constant Binder_Type :=
        (B_Name => New_Identifier (Name => "a"),
         B_Type => Ar_Type,
         others => <>);

      procedure Declare_Range_Type (Def : Node_Id;
                                    Count : Positive);

      procedure Declare_Range_Type (Def : Node_Id;
                                    Count : Positive) is
         Rng : constant Node_Id := Get_Range (Def);
         Rng_Type_Id : constant W_Identifier_Id :=
           Append_Num ("range_type", Count);
         Rng_Type : constant W_Primitive_Type_Id :=
           New_Abstract_Type (Name => Rng_Type_Id);
         B_Node : constant Node_Id := Base_Type (Etype (Def));
         B_Type : constant W_Primitive_Type_Id := +Type_Of_Node (B_Node);
         To_Int : constant W_Identifier_Id :=
           +Conversion_Name (+B_Type, +Int_Type);
         First_Term_I : constant W_Term_Id :=
           New_Call
             (Name => Append_Num (WNE_Array_First_Field, Count),
              Args => (1 => +A_Ident));
         First_Term : constant W_Term_Id :=
           New_Call
             (Name => To_Int,
              Args => (1 => +First_Term_I));
         Last_Term_I : constant W_Term_Id :=
           New_Call
             (Name => Append_Num (WNE_Array_Last_Field, Count),
              Args => (1 => +A_Ident));
         Last_Term : constant W_Term_Id :=
           New_Call
             (Name => To_Int,
              Args => (1 => +Last_Term_I));
      begin
         if Und_Ent /= Standard_String then
            Emit (Theory, New_Type (Name => Rng_Type_Id));
         end if;
         Emit (Theory,
           New_Function_Decl
             (Domain      => EW_Term,
              Name        => Append_Num (WNE_Array_First_Field, Count),
              Binders     =>
                (1 => (B_Name => A_Ident,
                       B_Type => Rng_Type,
                       others => <>)),
              Return_Type => B_Type));
         Emit (Theory,
           New_Function_Decl
             (Domain      => EW_Term,
              Name        => Append_Num (WNE_Array_Last_Field, Count),
              Binders     =>
                (1 => (B_Name => A_Ident,
                       B_Type => Rng_Type,
                       others => <>)),
              Return_Type => B_Type));
         Emit (Theory,
           New_Function_Decl
             (Domain => EW_Term,
              Name   => Append_Num ("mk", Count),
              Binders =>
                (1 => (B_Name => To_Ident (WNE_Array_First_Field),
                       B_Type => Int_Type,
                       others => <>),
                 2 => (B_Name => To_Ident (WNE_Array_Last_Field),
                       B_Type => Int_Type,
                       others => <>)),
              Return_Type => Rng_Type));
         if Is_Static_Range (Rng) then
            declare
               Low_Expr : constant W_Term_Id :=
                 New_Integer_Constant
                   (Value => Expr_Value (Low_Bound (Rng)));
               High_Expr : constant W_Term_Id :=
                 New_Integer_Constant
                   (Value => Expr_Value (High_Bound (Rng)));
            begin
               Emit
                 (Theory,
                  New_Axiom
                    (Name => Append_Num (WNE_Range_Axiom, Count),
                     Def  =>
                       New_Universal_Quantif
                         (Var_Type  => Rng_Type,
                          Variables => (1 => A_Ident),
                          Pred      =>
                            New_Connection
                              (Op   => EW_Imply,
                               Left =>
                                 New_Relation
                                   (Domain  => EW_Pred,
                                    Op_Type => EW_Int,
                                    Op      => EW_Le,
                                    Left    => +First_Term,
                                    Right   => +Last_Term),
                               Right =>
                                 New_And_Expr
                                   (Domain => EW_Pred,
                                    Left   => New_Range_Expr
                                      (Domain    => EW_Pred,
                                       Base_Type => EW_Int_Type,
                                       Low       => +Low_Expr,
                                       High      => +High_Expr,
                                       Expr      => +First_Term),
                                    Right  => New_Range_Expr
                                      (Domain    => EW_Pred,
                                       Base_Type => EW_Int_Type,
                                       Low       => +Low_Expr,
                                       High      => +High_Expr,
                                       Expr      => +Last_Term))))));
            end;
         end if;
      end Declare_Range_Type;
   begin
      declare
         --  in the "to" conversion, we need a field for "elts", and for
         --  each dimension, fields for first, last, offset
         To_Aggr : W_Field_Association_Array
           (1 .. Integer (Dimension) * 3 + 1);
         --  in the "from" conversion, we need a field for "elts", and for
         --  each dimension, a field for "offset"
         From_Aggr : W_Field_Association_Array
           (1 .. 2 * Integer (Dimension) + 1);
      begin
         To_Aggr (1) :=
           New_Field_Association
             (Field => Prefix (Array_Base, WNE_Array_Elts),
              Domain => EW_Term,
              Value =>
                New_Record_Access
                  (Name  => +A_Ident,
                   Field => To_Ident (WNE_Array_Elts)));
         From_Aggr (1) :=
           New_Field_Association
             (Field => To_Ident (WNE_Array_Elts),
              Domain => EW_Term,
              Value =>
                New_Record_Access
                  (Name => +A_Ident,
                   Field => Prefix (Array_Base, WNE_Array_Elts)));

         declare
            Index : Node_Id := First_Index (Und_Ent);
            Count : Positive := 1;
         begin
            while Present (Index) loop
               declare
                  B_Node : constant Node_Id := Base_Type (Etype (Index));
                  B_Type : constant W_Primitive_Type_Id :=
                    +Type_Of_Node (B_Node);
                  To_Int : constant W_Identifier_Id :=
                    +Conversion_Name (+B_Type, +Int_Type);
                  First_Term_I : constant W_Expr_Id :=
                    New_Call (Domain => EW_Term,
                              Name   =>
                                Append_Num (WNE_Array_First_Field, Count),
                              Args   =>
                                (1 =>
                                   New_Record_Access
                                     (Name  => +A_Ident,
                                      Field =>
                                        Append_Num
                                          (WNE_Range_Field, Count))));
                  First_Term : constant W_Expr_Id :=
                    New_Call
                      (Domain => EW_Term,
                       Name => To_Int,
                       Args => (1 => +First_Term_I));
                  Last_Term_I : constant W_Expr_Id :=
                    New_Call (Domain => EW_Term,
                              Name   =>
                                Append_Num (WNE_Array_Last_Field, Count),
                              Args   =>
                                (1 =>
                                   New_Record_Access
                                     (Name  => +A_Ident,
                                      Field =>
                                        Append_Num
                                          (WNE_Range_Field, Count))));
                  Last_Term : constant W_Expr_Id :=
                    New_Call
                      (Domain => EW_Term,
                       Name => To_Int,
                       Args => (1 => +Last_Term_I));
               begin
                  Declare_Range_Type (Index, Count);
                  To_Aggr (3 * Count - 1) :=
                    New_Field_Association
                      (Field =>
                           Append_Num (Array_Base,
                         WNE_Array_First_Field, Count),
                       Domain => EW_Term,
                       Value => First_Term);
                  To_Aggr (3 * Count) :=
                    New_Field_Association
                      (Field =>
                           Append_Num (Array_Base,
                         WNE_Array_Last_Field, Count),
                       Domain => EW_Term,
                       Value => Last_Term);
                  To_Aggr (3 * Count + 1) :=
                    New_Field_Association
                      (Field => Append_Num (Array_Base,
                       WNE_Array_Offset, Count),
                       Domain => EW_Term,
                       Value =>
                         New_Record_Access
                           (Name  => +A_Ident,
                            Field => Append_Num (WNE_Array_Offset, Count)));
                  From_Aggr (2 * Count) :=
                    New_Field_Association
                      (Field => Append_Num (WNE_Array_Offset, Count),
                       Domain => EW_Term,
                       Value =>
                         New_Record_Access
                           (Name => +A_Ident,
                            Field =>
                              Append_Num (Array_Base,
                                WNE_Array_Offset, Count)));
                  From_Aggr (2 * Count + 1) :=
                    New_Field_Association
                      (Field => Append_Num (WNE_Range_Field, Count),
                       Domain => EW_Term,
                       Value =>
                         New_Call
                           (Domain => EW_Term,
                            Name   => Append_Num ("mk", Count),
                            Args   =>
                              (1 =>
                                 New_Record_Access
                                   (Name  => +A_Ident,
                                    Field =>
                                      Append_Num
                                        (Array_Base,
                                         WNE_Array_First_Field,
                                         Count)),
                               2 =>
                                 New_Record_Access
                                   (Name  => +A_Ident,
                                    Field =>
                                      Append_Num
                                        (Array_Base,
                                         WNE_Array_Last_Field,
                                         Count)))));
                  Next_Index (Index);
                  Count := Count + 1;
               end;
            end loop;
         end;
         --  The type of standard strings has already been defined in the
         --  gnatprove standard files, we just make another alias to __string
         if Und_Ent = Standard_String then
            Emit (Theory,
              New_Type (Why3_Type_Name,
                Alias => New_Abstract_Type (Name => To_Ident (WNE_String))));
            Add_With_Clause (Theory,
                             "_gnatprove_standard_th",
                             "Main",
                             EW_Import,
                             EW_Theory);
         else
            declare
               Rec_Binders : Binder_Array (1 .. 2 * Integer (Dimension) + 1);
            begin
               Rec_Binders (1) :=
                 (B_Name => To_Ident (WNE_Array_Elts),
                  B_Type =>
                    New_Generic_Actual_Type_Chain
                      (Type_Chain => (1 => Comp_Type),
                       Name => Prefix (To_String (Array_Base), "map")),
                  others => <>);
               for Count in 1 .. Integer (Dimension) loop
                  Rec_Binders (2 * Count) :=
                    (B_Name => Append_Num (WNE_Array_Offset, Count),
                     B_Type => Int_Type,
                     others => <>);
                  Rec_Binders (2 * Count + 1) :=
                    (B_Name => Append_Num (WNE_Range_Field, Count),
                     B_Type =>
                       New_Abstract_Type (Name =>
                                            Append_Num
                                              (WNE_Range_Type, Count)),
                     others => <>);
               end loop;
               Emit
                 (Theory,
                  New_Record_Definition
                    (Name    => Why3_Type_Name,
                     Binders => Rec_Binders));
            end;
         end if;
         Emit
           (Theory,
            New_Function_Def
              (Domain      => EW_Term,
               Name        => Conv_To,
               Binders     =>
                 (1 => (B_Name => A_Ident,
                        B_Type => Name_Type,
                        others => <>)),
               Def         =>
                 New_Record_Aggregate (Associations => To_Aggr),
               Return_Type => Ar_Type));
         Emit
           (Theory,
            New_Function_Def
              (Domain      => EW_Term,
               Name        => Conv_From,
               Binders     => (1 => Ar_Binder),
               Return_Type => Name_Type,
               Def         =>
                 New_Record_Aggregate (Associations => From_Aggr)));
      end;
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
