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

with String_Utils;       use String_Utils;
with VC_Kinds;           use VC_Kinds;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Expr;       use Why.Gen.Expr;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Types;          use Why.Types;

package body Why.Gen.Arrays is

   -----------------------------------
   -- Declare_Ada_Constrained_Array --
   -----------------------------------

   procedure Declare_Ada_Constrained_Array
     (File       : W_File_Sections;
      Name       : String;
      Component  : String;
      First_List : W_Term_Array;
      Last_List  : W_Term_Array;
      Dimension  : Positive)
   is
      Ar         : constant W_Term_Id :=
                     New_Term ("a");
      Ar_Binder  : constant Binder_Type :=
                     (B_Name => New_Identifier ("a"),
                      B_Type =>
                        New_Abstract_Type
                          (Name => (New_Identifier (Name))),
                      others => <>);
   begin
      Declare_Ada_Unconstrained_Array (File, Name, Component, Dimension);

      --  State axioms about fixed 'First, 'Last and 'Length

      for Index in First_List'Range loop
         if First_List (Index) /= Why_Empty then
            declare
               Base_Name : constant String :=
                 (if Index = 1 then Name
                  else Name & "_" & Int_Image (Index));
            begin
               Emit
                 (File (W_File_Axiom),
                  New_Guarded_Axiom
                    (Name => Array_First_Static.Id (Base_Name),
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
                               UI_From_Int (Int (Index))),
                          Right   => +First_List (Index))));
            end;
         end if;
      end loop;
      for Index in Last_List'Range loop
         if Last_List (Index) /= Why_Empty then
            declare
               Base_Name : constant String :=
                 (if Index = 1 then Name
                  else Name & "_" & Int_Image (Index));
            begin
               Emit
                 (File (W_File_Axiom),
                  New_Guarded_Axiom
                    (Name => Array_Last_Static.Id (Base_Name),
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
                               UI_From_Int (Int (Index))),
                          Right   => +Last_List (Index))));
            end;
         end if;
      end loop;
   end Declare_Ada_Constrained_Array;

   -------------------------------------
   -- Declare_Ada_Unconstrained_Array --
   -------------------------------------

   procedure Declare_Ada_Unconstrained_Array
     (File      : W_File_Sections;
      Name      : String;
      Component : String;
      Dimension : Positive)
   is
      Comp_Type  : constant W_Primitive_Type_Id :=
                     New_Abstract_Type
                       (Name => (New_Identifier (Component)));
      Ar_Name    : constant String :=
         (if Dimension = 1 then Ada_Array
          else Ada_Array & "_" & Int_Image (Dimension));
      Ar_Type    : constant W_Primitive_Type_Id :=
                     New_Generic_Actual_Type_Chain
                       (Type_Chain => (1 => Comp_Type),
                        Name       => New_Identifier (Ar_Name));
      Name_Type  : constant W_Primitive_Type_Id :=
                     New_Abstract_Type
                       (Name => (New_Identifier (Name)));
      Ar         : constant W_Term_Id := New_Term ("a");
      Arb        : constant W_Term_Id := New_Term ("b");
      Ar_Binder_2 : constant Binder_Type :=
                      (B_Name => New_Identifier ("a"),
                       B_Type => Ar_Type,
                       others => <>);
   begin
      --  generate the theory:
      --  type t
      --  logic to_ : t -> comp ada_array
      --  logic from_ : comp ada_array -> t
      --  axiom 1 : forall x, to_ (from_ (x)) = x
      --  axiom 2 : forall x, y, to_ (x) = to_ (y) -> x = y
      --  ??? why-gen-axioms defines general methods to
      --  generate these axioms. Presumably not exactly those ones,
      --  but close enough. This should be factorized out.
      Emit (File (W_File_Logic_Type), New_Type (Name));
      Emit
        (File (W_File_Logic_Type),
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Array_Conv_From.Id (Name),
            Binders     => New_Binders ((1 => Name_Type)),
            Return_Type => Ar_Type));
      Emit
        (File (W_File_Logic_Type),
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Array_Conv_To.Id (Name),
            Binders     => (1 => Ar_Binder_2),
            Return_Type => Name_Type));
      Emit
        (File (W_File_Logic_Type),
         New_Axiom
           (Name => Array_Conv_Idem.Id (Name),
            Def  =>
              New_Universal_Quantif
                (Var_Type  =>
                   New_Abstract_Type
                     (Name => (New_Identifier (Name))),
                 Variables => (1 => New_Identifier ("a")),
                 Triggers  => New_Triggers
                   (Triggers =>
                      (1 =>
                         New_Trigger
                           (Terms =>
                              (1 =>
                                 New_Call
                                   (Name => Array_Conv_From.Id (Name),
                                    Args => (1 => +Ar)))))),
                 Pred      =>
                   New_Relation
                     (Op      => EW_Eq,
                      Op_Type => EW_Abstract,
                      Left    => +Ar,
                      Right   =>
                        New_Call
                          (Domain => EW_Term,
                           Name   => Array_Conv_To.Id (Name),
                           Args   =>
                             (1 =>
                                New_Call
                                  (Domain => EW_Term,
                                   Name   => Array_Conv_From.Id (Name),
                                   Args   => (1 => +Ar))))))));
      Emit
        (File (W_File_Logic_Type),
         New_Guarded_Axiom
           (Name    => Array_Conv_Idem_2.Id (Name),
            Binders => (1 => Ar_Binder_2),
            Def     =>
              New_Universal_Quantif
                (Var_Type  => +Ar_Type,
                 Variables => (1 => New_Identifier ("b")),
                 Triggers  =>
                   New_Triggers
                     (Triggers =>
                       (1 =>
                          New_Trigger
                            (Terms =>
                               (1 =>
                                  New_Call
                                    (Name => Array_Conv_To.Id (Name),
                                     Args => (1 => +Ar)),
                                2 =>
                                  New_Call
                                    (Name => Array_Conv_To.Id (Name),
                                     Args => (1 => +Arb)))))),
                 Pred      =>
                   New_Connection
                     (Op     => EW_Imply,
                      Left   =>
                        New_Relation
                          (Domain  => EW_Pred,
                           Op      => EW_Eq,
                           Op_Type => EW_Abstract,
                           Left    =>
                             New_Call
                               (Domain => EW_Term,
                                Name   => Array_Conv_To.Id (Name),
                                Args   => (1 => +Ar)),
                           Right =>
                             New_Call
                               (Domain => EW_Term,
                                Name   => Array_Conv_To.Id (Name),
                                Args   => (1 => +Arb))),
                      Right  =>
                        New_Relation
                          (Domain  => EW_Pred,
                           Op      => EW_Eq,
                           Op_Type => EW_Abstract,
                           Left    => +Ar,
                           Right   => +Arb)))));
   end Declare_Ada_Unconstrained_Array;

   ----------------------
   -- New_Array_Access --
   ----------------------

   function New_Array_Access
     (Ada_Node      : Node_Id;
      Type_Name     : String;
      Ar            : W_Expr_Id;
      Index         : W_Expr_Array;
      Domain        : EW_Domain;
      Dimension     : Positive) return W_Expr_Id
   is
      Base_Name : constant String :=
         (if Dimension = 1 then Ada_Array
          else Ada_Array & "_" & Int_Image (Dimension));
      Name      : constant W_Identifier_Id := Array_Access_Name.Id (Base_Name);
      Used_Name : constant W_Identifier_Id :=
         (if Domain = EW_Prog then To_Program_Space (Name) else Name);
      Progs     : constant W_Expr_Array :=
         Index & (1 => New_Call
                         (Domain => Domain,
                          Name   => Array_Conv_From.Id (Type_Name),
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
       Dimension : Positive;
       Argument  : Uint) return W_Expr_Id
   is
      Base_Name : constant String :=
         (if Dimension = 1 then Ada_Array
          else Ada_Array & "_" & Int_Image (Dimension));
      Attr_Str  : constant String := Attribute_Id'Image (Attr);
   begin
      UI_Image (Argument);
      declare
         Arg_Buf : constant String := UI_Image_Buffer (1 .. UI_Image_Length);
         Attr_Suff : constant String :=
            (if Argument = 1 then Attr_Str
             else Attr_Str & "_" & Arg_Buf);
      begin
         return
           New_Call
             (Domain => Domain,
              Name   => Attr_Name.Id (Base_Name, Attr_Suff),
              Args   =>
               (1 =>
                  New_Call
                    (Domain => Domain,
                     Name   => Array_Conv_From.Id (Type_Name),
                     Args   => (1 => +Ar))));
      end;
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
       Dimension : Positive) return W_Expr_Id
   is
      Base_Name : constant String :=
         (if Dimension = 1 then Ada_Array
          else Ada_Array & "_" & Int_Image (Dimension));
      Name : constant W_Identifier_Id := Array_Update_Name.Id (Base_Name);
      Used_Name : constant W_Identifier_Id :=
         (if Domain = EW_Prog then To_Program_Space (Name) else Name);
      Args : constant W_Expr_Array :=
         Index &
               (1 => New_Call
                       (Domain => Domain,
                        Name   => Array_Conv_From.Id (Type_Name),
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
          (Name   => Array_Conv_To.Id (Type_Name),
           Args   => (1 => Array_Upd),
           Domain => Domain);
   end New_Array_Update;

end Why.Gen.Arrays;
