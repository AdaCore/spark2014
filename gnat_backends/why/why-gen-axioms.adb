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
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Why.Unchecked_Ids;  use Why.Unchecked_Ids;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Types;      use Why.Gen.Types;

package body Why.Gen.Axioms is

   ---------------------------
   -- Define_Array_Eq_Axiom --
   ---------------------------

   procedure Define_Array_Eq_Axiom
      (File           : W_File_Id;
       Type_Name      : String;
       Index_Type     : W_Primitive_Type_Id;
       Component_Type : W_Primitive_Type_Id)
   is
      Ar_Name         : constant String := "a";
      Index_Name      : constant String := "i";
      Component_Name  : constant String := "v";
      Axiom_Body      : constant W_Predicate_Id :=
           New_Related_Terms
              (Left  =>
                 New_Array_Access_Term
                   (Type_Name => Type_Name,
                    Index => New_Term (Index_Name),
                    Ar =>
                      New_Array_Update_Term
                        (Type_Name => Type_Name,
                         Ar => New_Term (Ar_Name),
                         Index => New_Term (Index_Name),
                         Value => New_Term (Component_Name))),
               Op    => New_Rel_Eq,
               Right => New_Term (Component_Name));

      Quantified_Body : constant W_Predicate_Id :=
         New_Universal_Quantif
            (Variables => (1 => New_Identifier (Ar_Name)),
             Var_Type => New_Abstract_Type (Name => Type_Name),
             Pred =>
               New_Universal_Quantif
                 (Variables => (1 => New_Identifier (Index_Name)),
                  Var_Type => Index_Type,
                  Pred =>
                     New_Universal_Quantif
                       (Variables => (1 => New_Identifier (Component_Name)),
                        Var_Type => Component_Type,
                        Pred => Axiom_Body)));
   begin
      New_Axiom
         (File       => File,
          Name       => Array_Accupd_Eq_Axiom (Type_Name),
          Axiom_Body => Quantified_Body);
   end Define_Array_Eq_Axiom;

   -------------------------
   -- Define_Coerce_Axiom --
   -------------------------

   procedure Define_Coerce_Axiom
     (File           : W_File_Id;
      Type_Name      : W_Identifier_Id;
      Base_Type      : W_Primitive_Type_Id;
      From_Base_Type : W_Identifier_Id;
      To_Base_Type   : W_Identifier_Id)
   is
      Arg_S                : constant String := "x";
      X_To_Type_Op         : constant W_Operation_Unchecked_Id :=
                               New_Unchecked_Operation;
      Back_To_Base_Type_Op : constant W_Operation_Unchecked_Id :=
                               New_Unchecked_Operation;
      In_Range             : constant W_Operation_Unchecked_Id :=
                               New_Unchecked_Operation;
      Formula              : constant W_Implication_Unchecked_Id :=
                               New_Unchecked_Implication;
      Quantif_On_X         : constant W_Universal_Quantif_Unchecked_Id :=
                               New_Unchecked_Universal_Quantif;
   begin
      Operation_Set_Name (X_To_Type_Op, From_Base_Type);
      Operation_Append_To_Parameters (X_To_Type_Op,
                                      New_Term (Arg_S));

      Operation_Set_Name (Back_To_Base_Type_Op, To_Base_Type);
      Operation_Append_To_Parameters (Back_To_Base_Type_Op, X_To_Type_Op);

      Operation_Set_Name (In_Range, Range_Pred_Name (Type_Name));
      Operation_Append_To_Parameters (In_Range, New_Term (Arg_S));

      Implication_Set_Left (Formula, In_Range);
      Implication_Set_Right (Formula,
                             New_Related_Terms (Left  => Back_To_Base_Type_Op,
                                                Op    => New_Rel_Eq,
                                                Right => New_Term (Arg_S)));

      Universal_Quantif_Set_Var_Type (Quantif_On_X, Base_Type);
      Universal_Quantif_Append_To_Variables (Quantif_On_X,
                                             New_Identifier (Arg_S));

      New_Axiom
        (File       => File,
         Name       => Coerce_Axiom (Type_Name),
         Axiom_Body =>
            New_Universal_Predicate_Body ((1 => Quantif_On_X), Formula));
   end Define_Coerce_Axiom;

   ------------------------
   -- Define_Range_Axiom --
   ------------------------

   procedure Define_Range_Axiom
     (File       : W_File_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      Arg_S              : constant String := "x";
      Call_To_Conversion : constant W_Operation_Unchecked_Id :=
                             New_Unchecked_Operation;
      Formula            : constant W_Operation_Unchecked_Id :=
                             New_Unchecked_Operation;
      Quantif_On_X       : constant W_Universal_Quantif_Unchecked_Id :=
                             New_Unchecked_Universal_Quantif;
   begin
      Operation_Set_Name (Call_To_Conversion, Conversion);
      Operation_Append_To_Parameters (Call_To_Conversion, New_Term (Arg_S));

      Operation_Set_Name (Formula, Range_Pred_Name (Type_Name));
      Operation_Append_To_Parameters (Formula, Call_To_Conversion);

      Universal_Quantif_Set_Var_Type (Quantif_On_X,
                                      New_Abstract_Type (Name => Type_Name));
      Universal_Quantif_Append_To_Variables (Quantif_On_X,
                                             New_Identifier (Arg_S));

      New_Axiom
        (File       => File,
         Name       => Range_Axiom (Type_Name),
         Axiom_Body =>
            New_Universal_Predicate_Body ((1 => Quantif_On_X),
                                          Formula));
   end Define_Range_Axiom;

   --------------------------
   -- Define_Unicity_Axiom --
   --------------------------

   procedure Define_Unicity_Axiom
     (File       : W_File_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      X_S               : constant String := "x";
      Y_S               : constant String := "y";
      X_To_Base_Type_Op : constant W_Operation_Unchecked_Id :=
                            New_Unchecked_Operation;
      Y_To_Base_Type_Op : constant W_Operation_Unchecked_Id :=
                            New_Unchecked_Operation;
      Formula           : constant W_Implication_Unchecked_Id :=
                            New_Unchecked_Implication;
      Quantif_On_XY     : constant W_Universal_Quantif_Unchecked_Id :=
                            New_Unchecked_Universal_Quantif;
   begin
      Operation_Set_Name (X_To_Base_Type_Op, Conversion);
      Operation_Append_To_Parameters (X_To_Base_Type_Op, New_Term (X_S));

      Operation_Set_Name (Y_To_Base_Type_Op,
                          Duplicate_Any_Node (Id => Conversion));
      Operation_Append_To_Parameters (Y_To_Base_Type_Op, New_Term (Y_S));

      Implication_Set_Left (Formula,
                            New_Related_Terms (Left  => X_To_Base_Type_Op,
                                               Op    => New_Rel_Eq,
                                               Right => Y_To_Base_Type_Op));
      Implication_Set_Right (Formula,
                             New_Related_Terms (Left  => New_Term (X_S),
                                                Op    => New_Rel_Eq,
                                                Right => New_Term (Y_S)));

      Universal_Quantif_Set_Var_Type (Quantif_On_XY,
                                      New_Abstract_Type (Name => Type_Name));
      Universal_Quantif_Append_To_Variables (Quantif_On_XY,
                                             New_Identifier (X_S));
      Universal_Quantif_Append_To_Variables (Quantif_On_XY,
                                             New_Identifier (Y_S));

      New_Axiom
        (File       => File,
         Name       => Unicity_Axiom (Type_Name),
         Axiom_Body =>
            New_Universal_Predicate_Body ((1 => Quantif_On_XY),
                                          Formula));
   end Define_Unicity_Axiom;

end Why.Gen.Axioms;
