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

package body Why.Gen.Scalars is

   procedure Define_Scalar_Conversions
     (File           : W_File_Id;
      Name           : String;
      Base_Type      : W_Primitive_Type_Id;
      Base_Type_Name : String;
      First          : W_Term_Id;
      Last           : W_Term_Id);
   --  Given a type name, assuming that it ranges between First and Last,
   --  define conversions from this type to base type.

   -------------------------------------
   -- Declare_Ada_Abstract_Signed_Int --
   -------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int
     (File : W_File_Id;
      Name : String;
      Size : Uint) is
   begin
      Declare_Ada_Abstract_Signed_Int
        (File,
         Name,
         -2 ** (Size - 1),
         2 ** (Size - 1)  - 1);
   end Declare_Ada_Abstract_Signed_Int;

   procedure Declare_Ada_Abstract_Signed_Int
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint)
   is
   begin
      Emit (File, New_Type (Name));
      Define_Scalar_Conversions
        (File           => File,
         Name           => Name,
         Base_Type      => New_Base_Type (Base_Type => EW_Int),
         Base_Type_Name => "int",
         First          => New_Constant (First),
         Last           => New_Constant (Last));
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
        (File           => File,
         Name           => Name,
         Base_Type      => New_Base_Type (Base_Type => EW_Real),
         Base_Type_Name => "real",
         First          => New_Constant (First),
         Last           => New_Constant (Last));
   end Declare_Ada_Floating_Point;

   -------------------------------
   -- Define_Scalar_Conversions --
   -------------------------------

   procedure Define_Scalar_Conversions
     (File           : W_File_Id;
      Name           : String;
      Base_Type      : W_Primitive_Type_Id;
      Base_Type_Name : String;
      First          : W_Term_Id;
      Last           : W_Term_Id)
   is
      Arg_S : constant String := "n";
   begin
      Define_Range_Predicate (File, Name, Base_Type, First, Last);

      --  to base type:
      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => Conversion_To.Id (Name, Base_Type_Name),
            Binders        =>
              New_Binders
                ((1 => New_Abstract_Type
                         (Name => New_Identifier (Name)))),
            Return_Type => +Base_Type));

      --  from base type:
      declare
         Return_Type  : constant W_Primitive_Type_Id :=
                          New_Abstract_Type (Name => New_Identifier (EW_Term,
                                                                     Name));
         --  precondition: { <name>___in_range (n) }
         Range_Check  : constant W_Pred_Id :=
                          New_Call
                            (Domain => EW_Pred,
                             Name   => Range_Pred_Name.Id (Name),
                             Args   => (1 => +New_Term (Arg_S)));
         --  postcondition: { <name>___of_<base_type> (result) = n }
         Base_Result  : constant W_Term_Id :=
                          New_Call
                            (Domain => EW_Term,
                             Name   =>
                               Conversion_To.Id (Name,
                                                 Base_Type_Name),
                             Args   =>
                               (1 => +New_Result_Term));
         Post         : constant W_Pred_Id :=
                          New_Relation
                            (Domain => EW_Pred,
                             Left   => +Base_Result,
                             Op     => EW_Eq,
                             Right  => +New_Term (Arg_S));
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
            Name => Conversion_From.Id (Name, Base_Type_Name),
            Binders =>
              (1 => (B_Name => New_Identifier (Arg_S),
                     B_Type => Base_Type,
                     others => <>)),
            Return_Type => Return_Type,
            Spec => Spec);
         Define_Eq_Predicate (File, Name, Base_Type_Name);
         Define_Range_Axiom (File,
                             New_Identifier (Name),
                             Conversion_To.Id (Name, Base_Type_Name));
         Define_Coerce_Axiom (File,
                              New_Identifier (Name),
                              Base_Type,
                              Conversion_From.Id (Name, Base_Type_Name),
                              Conversion_To.Id (Name, Base_Type_Name));
         Define_Unicity_Axiom (File,
                               New_Identifier (Name),
                               Conversion_To.Id (Name, Base_Type_Name));
      end;
      New_Boolean_Equality_Parameter (File, Name);
   end Define_Scalar_Conversions;

end Why.Gen.Scalars;
