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
     (File         : W_File_Sections;
      Type_Name    : W_Identifier_Id;
      Base_Type    : W_Primitive_Type_Id;
      From         : W_Identifier_Id;
      To           : W_Identifier_Id;
      Hypothesis   : W_Pred_Id := Why_Empty;
      Modulus      : W_Term_OId := Why_Empty)
   is
      Arg_S                : constant W_Term_Id := New_Term ("x");
      X_To_Type_Op         : constant W_Term_Id :=
                               New_Call
                                 (Name => From,
                                  Args => (1 => +Arg_S));
      Back_To_Base_Type_Op : constant W_Term_Id :=
                               New_Call
                                 (Name => To,
                                  Args => (1 => +X_To_Type_Op));
      Normalized_Result    : constant W_Term_Id :=
                               (if Modulus = Why_Empty then
                                  Arg_S
                                else
                                  New_Call
                                    (Name => New_Integer_Mod.Id,
                                     Args => (+Arg_S, +Modulus)));
      Equality             : constant W_Pred_Id :=
                              New_Relation
                                (Op_Type => EW_Abstract,
                                 Left    => +Back_To_Base_Type_Op,
                                 Op      => EW_Eq,
                                 Right   => +Normalized_Result);
      Formula              : constant W_Pred_Id :=
                                 (if Hypothesis = Why_Empty then
                                    Equality
                                  else
                                    New_Connection
                                      (Op    => EW_Imply,
                                       Left  => +Hypothesis,
                                       Right => +Equality));
      Basic_Trigger        : constant W_Trigger_Id :=
         New_Trigger (Terms => (1 => +Back_To_Base_Type_Op));
      Enhanced_Triggers    : constant W_Triggers_OId :=
         (if Hypothesis = Why_Empty then
            New_Triggers (Triggers => (1 => Basic_Trigger))
          else
            New_Triggers (Triggers =>
               (1 => Basic_Trigger,
                2 => New_Trigger (Terms =>
                  (1 => +Hypothesis,
                   2 => +X_To_Type_Op)))));
      Quantif_On_X         : constant W_Pred_Id :=
                               New_Universal_Quantif
                                 (Var_Type  => Base_Type,
                                  Variables => (1 => New_Identifier (EW_Term,
                                                                     "x")),
                                  Triggers  => Enhanced_Triggers,
                                  Pred      => Formula);
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
           (Name => Coerce_Axiom.Id (Type_Name),
            Def  => Quantif_On_X));
   end Define_Coerce_Axiom;

   procedure Define_Coerce_Axiom
     (File      : W_File_Sections;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar;
      Modulus   : W_Term_OId := Why_Empty)
   is
      In_Range       : constant W_Pred_Id :=
                        New_Call
                           (Name => Range_Pred_Name.Id (Type_Name),
                            Args => (1 => +New_Term ("x")));
      Base_Type_Name : constant W_Identifier_Id :=
         New_Identifier (EW_Base_Type_Name (Base_Type));
   begin
      Define_Coerce_Axiom
        (File       => File,
         Type_Name  => Type_Name,
         Base_Type  => New_Base_Type (Base_Type => Base_Type),
         From       => Conversion_From.Id (Type_Name, Base_Type_Name),
         To         => Conversion_To.Id (Type_Name, Base_Type_Name),
         Hypothesis => In_Range,
         Modulus    => Modulus);
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
     (File       : W_File_Sections;
      Axiom_Name : W_Identifier_Id;
      Var_Type   : W_Primitive_Type_Id;
      Conversion : W_Identifier_Id)
   is
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
                                    Op_Type => EW_Abstract,
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
                              (Var_Type => Var_Type,
                               Variables =>
                                 (New_Identifier (X_S),
                                  New_Identifier (Y_S)),
                               Triggers =>
                                 New_Triggers (Triggers =>
                                    (1 => New_Trigger (Terms =>
                                       (1 => +X_To_Base_Type_Op,
                                        2 => +Y_To_Base_Type_Op)))),
                               Pred =>
                                 Formula);
   begin
      Emit
        (File (W_File_Axiom),
         New_Axiom
           (Name => Axiom_Name,
            Def  => Quantif_On_XY));
   end Define_Unicity_Axiom;

   procedure Define_Unicity_Axiom
     (File      : W_File_Sections;
      Type_Name : W_Identifier_Id;
      Base_Type : W_Identifier_Id)
   is
   begin
      Define_Unicity_Axiom
         (File       => File,
          Axiom_Name => Unicity_Axiom.Id (Type_Name),
          Var_Type   => New_Abstract_Type (Name => Type_Name),
          Conversion => Conversion_To.Id (Type_Name, Base_Type));
   end Define_Unicity_Axiom;

   procedure Define_Unicity_Axiom
     (File      : W_File_Sections;
      Type_Name : W_Identifier_Id;
      Base_Type : EW_Scalar) is
   begin
      Define_Unicity_Axiom
        (File      => File,
         Type_Name => Type_Name,
         Base_Type => New_Identifier (EW_Base_Type_Name (Base_Type)));
   end Define_Unicity_Axiom;

end Why.Gen.Axioms;
