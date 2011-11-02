------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       W H Y - G E N - A X I O M S                        --
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
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;

package body Why.Gen.Axioms is

   -------------------------
   -- Define_Coerce_Axiom --
   -------------------------

   procedure Define_Coerce_Axiom
     (File      : W_File_Sections;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar;
      Modulus   : W_Term_OId := Why_Empty)
   is
      Base_Type_Name       : constant W_Identifier_Id :=
                               New_Identifier
                                 (EW_Base_Type_Name (Base_Type));
      From_Base_Type       : constant W_Identifier_Id :=
                               Conversion_From.Id (Type_Name, Base_Type_Name);
      To_Base_Type         : constant W_Identifier_Id :=
                               Conversion_To.Id (Type_Name, Base_Type_Name);
      BT                   : constant W_Primitive_Type_Id
                               := New_Base_Type (Base_Type => Base_Type);
      Arg_S                : constant String := "x";
      X_To_Type_Op         : constant W_Term_Id :=
                               New_Call
                                 (Name => From_Base_Type,
                                  Args => (1 => +New_Term (Arg_S)));
      Back_To_Base_Type_Op : constant W_Term_Id :=
                               New_Call
                                 (Name => To_Base_Type,
                                  Args => (1 => +X_To_Type_Op));
      In_Range             : constant W_Pred_Id :=
                               New_Call
                                 (Name =>
                                    Range_Pred_Name.Id (Type_Name),
                                  Args =>
                                    (1 => +New_Term (Arg_S)));
      In_Range_t           : constant W_Term_Id :=
                               New_Call
                                 (Name =>
                                    Range_Pred_Name.Id (Type_Name),
                                  Args =>
                                    (1 => +New_Term (Arg_S)));
      Normalized_Result    : constant W_Term_Id :=
                               (if Modulus = Why_Empty then
                                  New_Term (Arg_S)
                                else
                                  New_Call
                                    (Name => New_Integer_Mod.Id,
                                     Args =>
                                       (+New_Term (Arg_S),
                                        +Modulus)));
      Formula              : constant W_Pred_Id :=
                               New_Connection
                                 (Op    => EW_Imply,
                                  Left  => +In_Range,
                                  Right =>
                                    New_Relation
                                      (Domain  => EW_Pred,
                                       Op_Type => Base_Type,
                                       Left    => +Back_To_Base_Type_Op,
                                       Op      => EW_Eq,
                                       Right   => +Normalized_Result));
      Quantif_On_X         : constant W_Pred_Id :=
                               New_Universal_Quantif
                                 (Var_Type  => BT,
                                  Variables => (1 => New_Identifier (EW_Term,
                                                                     Arg_S)),
                                  Triggers  => New_Triggers (
                                    Triggers =>
                                      (1 => New_Trigger (
                                         Terms => (1 => In_Range_t,
                                                   2 => X_To_Type_Op)),
                                       2 => New_Trigger (
                                         Terms => (1 =>
                                                     Back_To_Base_Type_Op)))),
                                  Pred      => Formula);
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
           (Name => Coerce_Axiom.Id (Type_Name),
            Def  => Quantif_On_X));
   end Define_Coerce_Axiom;

   ------------------------
   -- Define_Range_Axiom --
   ------------------------

   procedure Define_Range_Axiom
     (File       : W_File_Sections;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      Arg_S              : constant String := "x";
      Call_To_Conversion : constant W_Term_Id :=
                             New_Call
                               (Name => Conversion,
                                Args => (1 => +New_Term (Arg_S)));
      Formula            : constant W_Pred_Id :=
                             New_Call
                               (Name => Range_Pred_Name.Id (Type_Name),
                                Args => (1 => +Call_To_Conversion));
      Quantif_On_X       : constant W_Pred_Id :=
                             New_Universal_Quantif
                               (Var_Type =>
                                  New_Abstract_Type (Name => Type_Name),
                                Variables =>
                                  (1 => New_Identifier (Arg_S)),
                                Pred =>
                                  Formula);
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
           (Name => Range_Axiom.Id (Type_Name),
            Def  => Quantif_On_X));
   end Define_Range_Axiom;

   --------------------------
   -- Define_Unicity_Axiom --
   --------------------------

   procedure Define_Unicity_Axiom
     (File      : W_File_Sections;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar)
   is
      BT_Name           : constant W_Identifier_Id :=
                            New_Identifier
                              (EW_Base_Type_Name (Base_Type));
      Conversion        : constant W_Identifier_Id :=
                            Conversion_To.Id (Type_Name, BT_Name);
      X_S               : constant String := "x";
      Y_S               : constant String := "y";
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name => Conversion,
                               Args => (1 => +New_Term (X_S)));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Call
                              (Name => Conversion,
                               Args => (1 => +New_Term (Y_S)));
      Formula           : constant W_Pred_Id :=
                            New_Connection
                              (Op    => EW_Imply,
                               Left  =>
                                 New_Relation
                                   (Domain  => EW_Pred,
                                    Op_Type => Base_Type,
                                    Left    => +X_To_Base_Type_Op,
                                    Op      => EW_Eq,
                                    Right   => +Y_To_Base_Type_Op),
                               Right =>
                                 New_Relation
                                   (Domain  => EW_Pred,
                                    Op_Type => EW_Abstract,
                                    Left    => +New_Term (X_S),
                                    Op      => EW_Eq,
                                    Right   => +New_Term (Y_S)));
      Quantif_On_XY     : constant W_Pred_Id :=
                            New_Universal_Quantif
                              (Var_Type =>
                                 New_Abstract_Type (Name => Type_Name),
                               Variables =>
                                 (New_Identifier (X_S),
                                  New_Identifier (Y_S)),
                               Pred =>
                                 Formula);
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
           (Name => Unicity_Axiom.Id (Type_Name),
            Def  => Quantif_On_XY));
   end Define_Unicity_Axiom;

end Why.Gen.Axioms;
