------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
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

with Snames;             use Snames;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Funcs;      use Why.Gen.Funcs;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Terms;      use Why.Gen.Terms;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Consts;     use Why.Gen.Consts;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Conversions
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar;
      First     : W_Term_Id;
      Last      : W_Term_Id;
      Modulus   : W_Term_OId := Why_Empty);
   --  Given a type name, assuming that it ranges between First and Last,
   --  define conversions from this type to base type.

   procedure Define_Scalar_Attributes
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar;
      First     : W_Term_Id;
      Last      : W_Term_Id);

   ----------------------------------
   -- Declare_Ada_Abstract_Modular --
   ----------------------------------

   procedure Declare_Ada_Abstract_Modular
     (File    : W_File_Id;
      Name    : String;
      Modulus : Uint)
   is
   begin
      Emit (File, New_Type (Name));
      Define_Scalar_Conversions
        (File      => File,
         Name      => Name,
         Base_Type => EW_Int,
         First     => New_Constant (Uint_0),
         Last      => New_Constant (Modulus - 1),
         Modulus   => New_Constant (Modulus));
      Define_Scalar_Attributes
        (File      => File,
         Name      => Name,
         Base_Type => EW_Int,
         First     => New_Constant (Uint_0),
         Last      => New_Constant (Modulus - 1));
   end Declare_Ada_Abstract_Modular;

   -------------------------------------
   -- Declare_Ada_Abstract_Signed_Int --
   -------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint)
   is
   begin
      Emit (File, New_Type (Name));
      Define_Scalar_Conversions
        (File      => File,
         Name      => Name,
         Base_Type => EW_Int,
         First     => New_Constant (First),
         Last      => New_Constant (Last));
      Define_Scalar_Attributes
        (File      => File,
         Name      => Name,
         Base_Type => EW_Int,
         First     => New_Constant (First),
         Last      => New_Constant (Last));
   end Declare_Ada_Abstract_Signed_Int;

   --------------------------------
   -- Declare_Ada_Floating_Point --
   --------------------------------

   procedure Declare_Ada_Floating_Point
     (File  : W_File_Id;
      Name  : String;
      First : Ureal;
      Last  : Ureal) is
   begin
      Emit (File, New_Type (Name));
      Define_Scalar_Conversions
        (File      => File,
         Name      => Name,
         Base_Type => EW_Real,
         First     => New_Constant (First),
         Last      => New_Constant (Last));
      Define_Scalar_Attributes
        (File      => File,
         Name      => Name,
         Base_Type => EW_Real,
         First     => New_Constant (First),
         Last      => New_Constant (Last));
   end Declare_Ada_Floating_Point;

   -------------------------------
   -- Define_Scalar_Conversions --
   -------------------------------

   procedure Define_Scalar_Conversions
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar;
      First     : W_Term_Id;
      Last      : W_Term_Id;
      Modulus   : W_Term_OId := Why_Empty)
   is
      Signed  : constant Boolean := Modulus = Why_Empty;
      Arg_S   : constant String := "n";
      BT      : constant W_Primitive_Type_Id
                  := New_Base_Type (Base_Type => Base_Type);
      BT_Name : constant String := EW_Base_Type_Name (Base_Type);
   begin
      Define_Range_Predicate (File, Name, Base_Type, First, Last);

      --  to base type:
      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Conversion_To.Id (Name, BT_Name),
            Binders        =>
              New_Binders
                ((1 => New_Abstract_Type
                         (Name => New_Identifier (Name)))),
            Return_Type => BT));

      --  from base type:
      declare
         Return_Type  : constant W_Primitive_Type_Id :=
                          New_Abstract_Type (Name => New_Identifier (EW_Term,
                                                                     Name));
         --  precondition: { <name>___in_range (n) }
         Range_Check  : constant W_Pred_OId :=
                          (if Signed then
                             New_Call
                               (Domain => EW_Pred,
                                Name   => Range_Pred_Name.Id (Name),
                                Args   => (1 => +New_Term (Arg_S)))
                           else
                             Why_Empty);
         --  postcondition: { <name>___of_<base_type> (result) = n }
         Base_Result  : constant W_Term_Id :=
                          New_Call
                            (Domain => EW_Term,
                             Name   =>
                               Conversion_To.Id (Name,
                                                 BT_Name),
                             Args   =>
                               (1 => +New_Result_Term));
         Post         : constant W_Pred_Id :=
                          New_Relation
                            (Domain  => EW_Pred,
                             Op_Type => Base_Type,
                             Left    => +Base_Result,
                             Op      => EW_Eq,
                             Right   => +New_Term (Arg_S));
         Spec         : constant Declaration_Spec_Array :=
                          (1 => (Kind   => W_Function_Decl,
                                 Domain => EW_Term,
                                 others => <>),
                           2 => (Kind   => W_Function_Decl,
                                 Domain => EW_Prog,
                                 Pre    => Range_Check,
                                 Post   => Post,
                                 others => <>));

      begin
         Emit_Top_Level_Declarations
           (File => File,
            Name => Conversion_From.Id (Name, BT_Name),
            Binders =>
              (1 => (B_Name => New_Identifier (Arg_S),
                     B_Type => BT,
                     others => <>)),
            Return_Type => Return_Type,
            Spec => Spec);
         Define_Eq_Predicate (File, Name, Base_Type);
         Define_Range_Axiom (File,
                             New_Identifier (Name),
                             Conversion_To.Id (Name, BT_Name));
         Define_Coerce_Axiom (File,
                              New_Identifier (Name),
                              Base_Type,
                              Modulus);
         Define_Unicity_Axiom (File,
                               New_Identifier (Name),
                               Base_Type);
      end;
      New_Boolean_Equality_Parameter (File, Name);
   end Define_Scalar_Conversions;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (File      : W_File_Id;
      Name      : String;
      Base_Type : EW_Scalar;
      First     : W_Term_Id;
      Last      : W_Term_Id)
   is
      type Scalar_Attr is (S_First, S_Last);

      type Attr_Info is record
         Attr_Id : Attribute_Id;
         Value   : W_Term_Id;
      end record;

      Attr_Values : constant array (Scalar_Attr) of Attr_Info :=
                      (S_First => (Attribute_First, First),
                       S_Last  => (Attribute_Last, Last));
   begin
      for J in Attr_Values'Range loop
         Emit_Top_Level_Declarations
           (File        => File,
            Name        =>
              Attr_Name.Id
                (Name,
                 Attribute_Id'Image (Attr_Values (J).Attr_Id)),
            Binders     => (1 .. 0 => <>),
            Return_Type => New_Base_Type (Base_Type => Base_Type),
            Spec        =>
              (1 =>
                 (Kind   => W_Function_Decl,
                  Domain => EW_Term,
                  Def    => Attr_Values (J).Value,
                  others => <>)));
      end loop;
   end Define_Scalar_Attributes;

end Why.Gen.Scalars;
