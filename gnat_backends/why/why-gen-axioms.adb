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

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;

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
         New_Equal
           (Left => New_Array_Access_Term
                      (Type_Name => Type_Name,
                       Index => New_Term (Index_Name),
                       Ar =>
                         New_Array_Update_Term
                           (Type_Name => Type_Name,
                            Ar => New_Term (Ar_Name),
                            Index => New_Term (Index_Name),
                            Value => New_Term (Component_Name))),
            Right => New_Term (Component_Name));

      Quantified_Body : constant W_Predicate_Id :=
         New_Universal_Quantif
            (Variables => (1 => New_Identifier (Ar_Name)),
             Var_Type  =>
               New_Abstract_Type (Name => New_Identifier (Type_Name)),
             Pred      =>
               New_Universal_Quantif
                 (Variables => (1 => New_Identifier (Index_Name)),
                  Var_Type  => Index_Type,
                  Pred      =>
                     New_Universal_Quantif
                       (Variables => (1 => New_Identifier (Component_Name)),
                        Var_Type  => Component_Type,
                        Pred      => Axiom_Body)));

   begin
      New_Axiom
         (File       => File,
          Name       => Array_Accupd_Eq_Axiom (Type_Name),
          Axiom_Body => Quantified_Body);
   end Define_Array_Eq_Axiom;

   ----------------------------
   -- Define_Array_Neq_Axiom --
   ----------------------------

   procedure Define_Array_Neq_Axiom
      (File           : W_File_Id;
       Type_Name      : String;
       Index_Type     : W_Primitive_Type_Id;
       Component_Type : W_Primitive_Type_Id)
   is
      Ar_Name         : constant String := "a";
      Index1          : constant String := "i";
      Index2          : constant String := "j";
      Component_Name  : constant String := "v";
      Conclusion      : constant W_Predicate_Id :=
         New_Equal
           (Left =>
              New_Array_Access_Term
                (Type_Name => Type_Name,
                 Index => New_Term (Index1),
                 Ar =>
                   New_Array_Update_Term
                     (Type_Name => Type_Name,
                      Ar => New_Term (Ar_Name),
                      Index => New_Term (Index2),
                      Value => New_Term (Component_Name))),
            Right =>
               New_Array_Access_Term
                 (Type_Name => Type_Name,
                  Index => New_Term (Index1),
                  Ar => New_Term (Ar_Name)));

      Hypothesis     : constant W_Predicate_Id :=
            New_NEqual (New_Term (Index1), New_Term (Index2));

      Axiom_Body     : constant W_Predicate_Id :=
            New_Implication (Left => Hypothesis, Right =>  Conclusion);

      Quantified_Body : constant W_Predicate_Id :=
         New_Universal_Quantif
            (Variables => (1 => New_Identifier (Ar_Name)),
             Var_Type =>
               New_Abstract_Type (Name => New_Identifier (Type_Name)),
             Pred =>
               New_Universal_Quantif
                 (Variables =>
                     (1 => New_Identifier (Index1),
                      2 => New_Identifier (Index2)),
                  Var_Type => Index_Type,
                  Pred =>
                     New_Universal_Quantif
                       (Variables => (1 => New_Identifier (Component_Name)),
                        Var_Type => Component_Type,
                        Pred => Axiom_Body)));
   begin
      New_Axiom
         (File       => File,
          Name       => Array_Accupd_Neq_Axiom (Type_Name),
          Axiom_Body => Quantified_Body);
   end Define_Array_Neq_Axiom;

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
      X_To_Type_Op         : constant W_Term_Id :=
                               New_Operation
                                 (Name       => From_Base_Type,
                                  Parameters => (1 => New_Term (Arg_S)));
      Back_To_Base_Type_Op : constant W_Term_Id :=
                               New_Operation
                                 (Name       => To_Base_Type,
                                  Parameters => (1 => X_To_Type_Op));
      In_Range             : constant W_Predicate_Id :=
                               New_Predicate_Instance
                                  (Name       => Range_Pred_Name (Type_Name),
                                   Parameters => (1 => New_Term (Arg_S)));
      In_Range_t          : constant W_Term_Id :=
                               New_Operation
                                  (Name       => Range_Pred_Name (Type_Name),
                                   Parameters => (1 => New_Term (Arg_S)));
      Formula              : constant W_Predicate_Id :=
                               New_Implication
                                 (Left  => In_Range,
                                  Right =>
                                    New_Related_Terms
                                      (Left  => Back_To_Base_Type_Op,
                                       Op    => New_Rel_Eq,
                                       Right => New_Term (Arg_S)));
      Quantif_On_X         : constant W_Predicate_Id :=
                               New_Universal_Quantif
                                 (Var_Type  => Base_Type,
                                  Variables => (1 => New_Identifier (Arg_S)),
                                  Triggers  => New_Triggers (
                                    Triggers =>
                                      (1 => New_Trigger (
                                         Terms => (1 => In_Range_t)),
                                       2 => New_Trigger (
                                         Terms => (1 => X_To_Type_Op)))),
                                  Pred      => Formula);
   begin
      New_Axiom
        (File       => File,
         Name       => Coerce_Axiom (Type_Name),
         Axiom_Body => Quantif_On_X);
   end Define_Coerce_Axiom;

   -------------------------
   -- Define_Getter_Axiom --
   -------------------------

   procedure Define_Getter_Axiom
     (File      : W_File_Id;
      Type_Name : String;
      C_Name    : String;
      C_Names   : String_Lists.List;
      Builder   : W_Logic_Type_Id)
   is
      use String_Lists;

      Call_To_Builder : constant W_Term_Id :=
                          New_Operation
                            (Name       => Record_Builder_Name (Type_Name),
                             Parameters => New_Terms (C_Names));
      Call_To_Getter  : constant W_Term_Id :=
                          New_Operation
                           (Name       => Record_Getter_Name (C_Name),
                            Parameters => (1 => Call_To_Builder));
      Context         : constant W_Predicate_Id :=
                          New_Equal (Call_To_Getter,
                                     New_Term (C_Name));
      UPB             : constant W_Predicate_Id :=
                          New_Universal_Predicate (C_Names,
                                                   Builder,
                                                   Context);
   begin
      New_Axiom
        (File       => File,
         Name       => Record_Getter_Axiom (C_Name),
         Axiom_Body => UPB);
   end Define_Getter_Axiom;

   ------------------------
   -- Define_Range_Axiom --
   ------------------------

   procedure Define_Range_Axiom
     (File       : W_File_Id;
      Type_Name  : W_Identifier_Id;
      Conversion : W_Identifier_Id)
   is
      Arg_S              : constant String := "x";
      Call_To_Conversion : constant W_Term_Id :=
                             New_Operation
                               (Name       => Conversion,
                                Parameters => (1 => New_Term (Arg_S)));
      Formula            : constant W_Predicate_Id :=
                             New_Predicate_Instance
                               (Name       => Range_Pred_Name (Type_Name),
                                Parameters => (1 => Call_To_Conversion));
      Quantif_On_X       : constant W_Predicate_Id :=
                             New_Universal_Quantif
                               (Var_Type =>
                                  New_Abstract_Type (Name => Type_Name),
                                Variables =>
                                  (1 => New_Identifier (Arg_S)),
                                Pred =>
                                  Formula);
   begin
      New_Axiom
        (File       => File,
         Name       => Range_Axiom (Type_Name),
         Axiom_Body => Quantif_On_X);
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
      X_To_Base_Type_Op : constant W_Term_Id :=
                            New_Operation (Name =>
                                             Conversion,
                                           Parameters =>
                                             (1 => New_Term (X_S)));
      Y_To_Base_Type_Op : constant W_Term_Id :=
                            New_Operation (Name =>
                                             +Duplicate_Any_Node
                                               (Id => +Conversion),
                                           Parameters =>
                                             (1 => New_Term (Y_S)));
      Formula           : constant W_Predicate_Id :=
                            New_Implication
                              (Left =>
                                 New_Related_Terms
                                   (Left  => X_To_Base_Type_Op,
                                    Op    => New_Rel_Eq,
                                    Right => Y_To_Base_Type_Op),
                               Right =>
                                 New_Related_Terms (Left  => New_Term (X_S),
                                                    Op    => New_Rel_Eq,
                                                    Right => New_Term (Y_S)));
      Quantif_On_XY     : constant W_Predicate_Id :=
                            New_Universal_Quantif
                              (Var_Type =>
                                 New_Abstract_Type (Name => Type_Name),
                               Variables =>
                                 (New_Identifier (X_S),
                                  New_Identifier (Y_S)),
                               Pred =>
                                 Formula);
   begin
      New_Axiom
        (File       => File,
         Name       => Unicity_Axiom (Type_Name),
         Axiom_Body => Quantif_On_XY);
   end Define_Unicity_Axiom;

end Why.Gen.Axioms;
