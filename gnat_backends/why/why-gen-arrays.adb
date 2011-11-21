------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - A R R A Y S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
with Gnat2Why.Expr;      use Gnat2Why.Expr;
--  ??? because of Get_Range, which should be moved

with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with Stand;              use Stand;
with String_Utils;       use String_Utils;
with VC_Kinds;           use VC_Kinds;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Binders;    use Why.Gen.Binders;

package body Why.Gen.Arrays is

   procedure Define_In_Range_Axiom
     (File       : W_File_Sections;
      Type_Name  : String;
      Index_Name : String;
      Dimension  : Pos;
      Argument   : Uint);

   -----------------------------------
   -- Declare_Ada_Constrained_Array --
   -----------------------------------

   procedure Declare_Ada_Constrained_Array
     (File       : W_File_Sections;
      Entity     : Entity_Id)
   is
      Name       : constant String := Full_Name (Entity);
      Dimension  : constant Pos := Number_Dimensions (Entity);
      Ar         : constant W_Term_Id := New_Term ("a");
      Ar_Binder  : constant Binder_Type :=
                     (B_Name => New_Identifier ("a"),
                      B_Type =>
                        New_Abstract_Type
                          (Name => (New_Identifier (Name))),
                      others => <>);
      Index      : Node_Id := First_Index (Entity);
      Count      : Positive := 1;
   begin
      Declare_Ada_Unconstrained_Array (File, Entity);

      --  State axioms about fixed 'First, 'Last and 'Length

      while Present (Index) loop
         declare
            Rng  : constant Node_Id := Get_Range (Index);
            Low  : constant Node_Id := Low_Bound (Rng);
            High : constant Node_Id := High_Bound (Rng);
         begin
            if Is_Static_Expression (Low) then
               Emit
                 (File (W_File_Axiom),
                  New_Guarded_Axiom
                    (Name =>
                       Array_First_Static.Id (Add_Int_Suffix (Name, Count)),
                     Binders => (1 => Ar_Binder),
                     Def =>
                       New_Relation
                         (Op      => EW_Eq,
                          Op_Type => EW_Int,
                          Left    =>
                            +New_Array_Attr
                              (Attribute_First,
                               Name,
                               +Ar,
                               EW_Term,
                               Dimension,
                               UI_From_Int (Int (Count))),
                          Right   => New_Integer_Constant
                                       (Value => Expr_Value (Low)))));
            end if;
            if Is_Static_Expression (High) then
               Emit
                 (File (W_File_Axiom),
                  New_Guarded_Axiom
                    (Name =>
                       Array_Last_Static.Id (Add_Int_Suffix (Name, Count)),
                     Binders => (1 => Ar_Binder),
                     Def =>
                       New_Relation
                         (Op      => EW_Eq,
                          Op_Type => EW_Int,
                          Left    =>
                            +New_Array_Attr
                              (Attribute_Last,
                               Name,
                               +Ar,
                               EW_Term,
                               Dimension,
                               UI_From_Int (Int (Count))),
                          Right   => New_Integer_Constant
                                       (Value => Expr_Value (High)))));
            end if;
            Next_Index (Index);
            Count := Count + 1;
         end;
      end loop;
   end Declare_Ada_Constrained_Array;

   -------------------------------------
   -- Declare_Ada_Unconstrained_Array --
   -------------------------------------

   procedure Declare_Ada_Unconstrained_Array
     (File       : W_File_Sections;
      Entity : Entity_Id)
   is
      Name       : constant String := Full_Name (Entity);
      Component  : constant String := Full_Name (Component_Type (Entity));
      Dimension  : constant Pos := Number_Dimensions (Entity);
      Type_Id     : constant W_Identifier_Id := New_Identifier (Name);
      BT_Str      : constant String := New_Ada_Array_Name (Dimension);
      BT_Id       : constant W_Identifier_Id := New_Identifier (BT_Str);
      Comp_Type   : constant W_Primitive_Type_Id :=
                     New_Abstract_Type
                       (Name => (New_Identifier (Component)));
      Ar_Type     : constant W_Primitive_Type_Id :=
                     New_Generic_Actual_Type_Chain
                       (Type_Chain => (1 => Comp_Type),
                        Name       => BT_Id);
      Name_Type   : constant W_Primitive_Type_Id :=
                     New_Abstract_Type (Name => Type_Id);
      Ar_Binder_2 : constant Binder_Type :=
                      (B_Name => New_Identifier ("a"),
                       B_Type => Ar_Type,
                       others => <>);
      Conv_From   : constant W_Identifier_Id :=
                      Conversion_From.Id (Name, BT_Str);
      Conv_To     : constant W_Identifier_Id :=
                      Conversion_To.Id (Name, BT_Str);
   begin
      --  generate the theory:
      --  type t
      --  logic to_ : t -> comp ada_array
      --  logic from_ : comp ada_array -> t
      --  axiom 1 : forall x, to_ (from_ (x)) = x
      --  axiom 2 : forall x, y, to_ (x) = to_ (y) -> x = y
      Emit (File (W_File_Logic_Type), New_Type (Name));
      Emit
        (File (W_File_Logic_Type),
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Conv_To,
            Binders     => New_Binders ((1 => Name_Type)),
            Return_Type => Ar_Type));
      Emit
        (File (W_File_Logic_Type),
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Conv_From,
            Binders     => (1 => Ar_Binder_2),
            Return_Type => Name_Type));
      Define_Coerce_Axiom
         (File      => File,
          Type_Name => Type_Id,
          Base_Type => Ar_Type,
          From      => Conv_From,
          To        => Conv_To);
      Define_Unicity_Axiom
        (File       => File,
         Axiom_Name => Unicity_Axiom.Id (Name),
         Var_Type   => Ar_Type,
         Conversion => Conversion_From.Id (Name, BT_Str));
      declare
         Arg   : Uint := Uint_1;
         Index : Node_Id := First_Index (Entity);
      begin
         while Present (Index) loop
            declare
               Index_Entity : constant Entity_Id := Etype (Index);
            begin
               if Index_Entity /= Standard_Boolean then
                  Define_In_Range_Axiom
                    (File       => File,
                     Type_Name  => Name,
                     Index_Name => Full_Name (Index_Entity),
                     Dimension  => Dimension,
                     Argument   => Arg);
               end if;
            end;
            Arg := Arg + Uint_1;
            Next_Index (Index);
         end loop;
      end;
   end Declare_Ada_Unconstrained_Array;

   ---------------------------
   -- Define_In_Range_Axiom --
   ---------------------------

   procedure Define_In_Range_Axiom
     (File       : W_File_Sections;
      Type_Name  : String;
      Index_Name : String;
      Dimension  : Pos;
      Argument   : Uint)
   is
      Var            : constant W_Identifier_Id :=
         New_Identifier ("x");
      First_Term     : constant W_Term_Id :=
               +New_Array_Attr (Attribute_First,
                                Type_Name,
                                +Var,
                                EW_Term,
                                Dimension,
                                Argument);
      Last_Term      : constant W_Term_Id :=
               +New_Array_Attr (Attribute_Last,
                                Type_Name,
                                +Var,
                                EW_Term,
                                Dimension,
                                Argument);
      Precond        : constant W_Pred_Id :=
               New_Relation
                  (Op_Type => EW_Bool,
                   Left    => +First_Term,
                   Right   => +Last_Term,
                   Op      => EW_Le);
      First_In_Range : constant W_Pred_Id :=
               New_Call (Name => Range_Pred_Name.Id (Index_Name),
                         Args => (1 => +First_Term));
      Last_In_Range  : constant W_Pred_Id :=
               New_Call (Name => Range_Pred_Name.Id (Index_Name),
                         Args => (1 => +Last_Term));
      Conclusion     : constant W_Pred_Id :=
         New_Connection
            (Op    => EW_And,
             Left  => +First_In_Range,
             Right => +Last_In_Range);
      Formula        : constant W_Pred_Id :=
         New_Connection
            (Op    => EW_Imply,
             Left  => +Precond,
             Right => +Conclusion);
      Quantif        : constant W_Pred_Id :=
         New_Universal_Quantif
            (Var_Type  =>
               New_Abstract_Type (Name => New_Identifier (Type_Name)),
             Variables => (1 => Var),
             Pred => Formula);
      Axiom_Base     : constant String := Type_Name & "__index_in_range";
      Axiom_Name     : constant String :=
         (if Argument = Uint_1 then Axiom_Base
          else Axiom_Base & "_" & Uint_Image (Argument));
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
            (Name => New_Identifier (Axiom_Name),
             Def  => Quantif));
   end Define_In_Range_Axiom;

   ----------------------
   -- New_Array_Access --
   ----------------------

   function New_Array_Access
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Expr_Id;
      Index         : W_Expr_Array;
      Domain        : EW_Domain;
      Dimension     : Pos) return W_Expr_Id
   is
      BT_Str    : constant String := New_Ada_Array_Name (Dimension);
      Name      : constant W_Identifier_Id := Array_Access_Name.Id (BT_Str);
      Used_Name : constant W_Identifier_Id :=
         (if Domain = EW_Prog then To_Program_Space (Name) else Name);
      Progs     : constant W_Expr_Array :=
         Index & (1 => New_Call
                         (Domain => Domain,
                          Name   => Conversion_To.Id (Type_Name, BT_Str),
                          Args   => (1 => +Ar)));
   begin
      return
         +New_Located_Call
            (Ada_Node => Ada_Node,
             Reason   => VC_Array_Bounds_Check,
             Name     => Used_Name,
             Domain   => Domain,
             Progs    => Progs);
   end New_Array_Access;

   --------------------
   -- New_Array_Attr --
   --------------------

   function New_Array_Attr
      (Attr      : Attribute_Id;
       Type_Name : String;
       Ar        : W_Expr_Id;
       Domain    : EW_Domain;
       Dimension : Pos;
       Argument  : Uint) return W_Expr_Id
   is
      Attr_Str  : constant String := Attribute_Id'Image (Attr);

      --  ??? The logic to obtain the right suffix (_2, _3 etc) is duplicated
      --  here because of the usage of Uint. Should be fixed.

      Attr_Suff : constant String :=
         (if Argument = Uint_1 then Attr_Str
          else Attr_Str & "_" & Uint_Image (Argument));
      BT_Str  : constant String := New_Ada_Array_Name (Dimension);
   begin

      return
        New_Call
          (Domain => Domain,
           Name   =>
             Attr_Name.Id (BT_Str, Attr_Suff),
           Args   =>
            (1 =>
               New_Call
                 (Domain => Domain,
                  Name   => Conversion_To.Id (Type_Name, BT_Str),
                  Args   => (1 => +Ar))));
   end New_Array_Attr;

   ----------------------
   -- New_Array_Update --
   ----------------------

   function New_Array_Update
      (Ada_Node  : Node_Id;
       Type_Name : String;
       Ar        : W_Expr_Id;
       Index     : W_Expr_Array;
       Value     : W_Expr_Id;
       Domain    : EW_Domain;
       Dimension : Pos) return W_Expr_Id
   is
      BT_Str    : constant String := New_Ada_Array_Name (Dimension);
      Name      : constant W_Identifier_Id := Array_Update_Name.Id (BT_Str);
      Used_Name : constant W_Identifier_Id :=
         (if Domain = EW_Prog then To_Program_Space (Name) else Name);
      Args : constant W_Expr_Array :=
         Index &
               (1 => New_Call
                       (Domain => Domain,
                        Name   => Conversion_To.Id (Type_Name, BT_Str),
                        Args   => (1 => +Ar)),
                2 => +Value);
      Array_Upd : constant W_Expr_Id :=
         New_Located_Call
           (Ada_Node => Ada_Node,
            Domain => Domain,
            Reason => VC_Array_Bounds_Check,
            Name   => Used_Name,
            Progs   => Args);
   begin
      return
        New_Call
          (Name   => Conversion_From.Id (Type_Name, BT_Str),
           Args   => (1 => Array_Upd),
           Domain => Domain);
   end New_Array_Update;

end Why.Gen.Arrays;
