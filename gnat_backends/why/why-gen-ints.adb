------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         W H Y - G E N - I N T S                          --
--                                                                          --
--                                 S p e c                                  --
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
with Why.Sinfo;          use Why.Sinfo;

package body Why.Gen.Ints is

   procedure Define_Signed_Int_Conversions
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint);

   ---------------------------------
   -- Declare_Abstract_Signed_Int --
   ---------------------------------

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
      New_Abstract_Type (File, Name);
      Define_Signed_Int_Conversions (File, Name, First, Last);
   end Declare_Ada_Abstract_Signed_Int;

   -----------------------------------
   -- Define_Signed_Int_Conversions --
   -----------------------------------

   procedure Define_Signed_Int_Conversions
     (File  : W_File_Id;
      Name  : String;
      First : Uint;
      Last  : Uint)
   is
      Arg_S : constant String := "n";

   begin
      Define_Range_Predicate (File, Name, First, Last);

      --  to int:
      New_Logic
         (File        => File,
          Name        => New_Conversion_To_Int.Id (Name),
          Args        =>
            (1 => New_Abstract_Type (Name => New_Identifier (Name))),
          Return_Type => New_Type_Int);

      --  from int:
      declare
         Return_Type : constant W_Logic_Return_Type_Id :=
                         New_Abstract_Type (Name => New_Identifier (Name));
         --  precondition: { <name>___in_range (n) }
         Range_Check : constant W_Predicate_Id :=
                         New_Predicate_Instance (Name =>
                                                   Range_Pred_Name.Id (Name),
                                                 Parameters =>
                                                   (1 => New_Term (Arg_S)));
         --  postcondition: { <name>___of_integer (result) = n }
         Int_Result  : constant W_Operation_Id :=
                         New_Operation (Name =>
                                          New_Conversion_To_Int.Id (Name),
                                        Parameters =>
                                          (1 => New_Result_Term));
         Post        : constant W_Predicate_Id :=
                         New_Related_Terms (Left  => +Int_Result,
                                            Op    => New_Rel_Eq,
                                            Right => New_Term (Arg_S));
         Spec        : Declaration_Spec_Array :=
                         (1 => (Kind => W_Logic,
                                others => <>),
                          2 => (Kind => W_Parameter_Declaration,
                                Pre  => Range_Check,
                                Post => Post,
                                others => <>));

      begin
         Emit_Top_Level_Declarations
           (File => File,
            Name => New_Conversion_From_Int.Id (Name),
            Binders =>
              (1 => (B_Name => New_Identifier (Arg_S),
                     B_Type => New_Type_Int,
                     others => <>)),
            Return_Type => +Return_Type,
            Spec => Spec);
         Define_Eq_Predicate (File, Name);
         Define_Range_Axiom (File,
                             New_Identifier (Name),
                             New_Conversion_To_Int.Id (Name));
         Define_Coerce_Axiom (File,
                              New_Identifier (Name),
                              New_Type_Int,
                              New_Conversion_From_Int.Id (Name),
                              New_Conversion_To_Int.Id (Name));
         Define_Unicity_Axiom (File,
                               New_Identifier (Name),
                               New_Conversion_To_Int.Id (Name));
      end;
      New_Boolean_Equality_Parameter (File, Name);
   end Define_Signed_Int_Conversions;

   ----------------------------------------
   -- Declare_Boolean_Integer_Comparison --
   ----------------------------------------

   procedure Declare_Boolean_Integer_Comparison
     (File : W_File_Id)
   is
   begin
      for Rel_Symbol in W_Relation'Range loop
         New_Logic
           (File => File,
            Name => New_Bool_Int_Cmp (Rel_Symbol),
            Args =>
               (1 => New_Type_Int,
                2 => New_Type_Int),
            Return_Type => New_Type_Bool);
         declare
            X_S        : constant String := "x";
            Y_S        : constant String := "y";
            True_Pred : constant W_Predicate_Id :=
               New_Related_Terms
                  (Left  => New_Term (X_S),
                   Op    => New_Rel_Symbol (Rel_Symbol),
                   Right => New_Term (Y_S));
            False_Pred : constant W_Predicate_Id :=
                           New_Negation (Operand => True_Pred);
            Axiom_Body : constant W_Predicate_Id :=
              New_Universal_Quantif
                (Variables =>
                     (1 => New_Identifier (X_S),
                      2 => New_Identifier (Y_S)),
                 Var_Type => New_Type_Int,
                 Pred =>
                   New_Conjunction
                     (Left => New_Implication
                          (Left =>
                               New_Equal
                             (Left  => New_Operation
                                (Name => New_Bool_Int_Cmp (Rel_Symbol),
                                 Parameters =>
                                   (1 => New_Term (Name => X_S),
                                    2 => New_Term (Name => Y_S))),
                              Right => New_Term ("true")),
                           Right => True_Pred),
                      Right => New_Implication
                        (Left =>
                           New_Equal
                             (Left  => New_Operation
                                  (Name => New_Bool_Int_Cmp (Rel_Symbol),
                                   Parameters =>
                                     (1 => New_Term (Name => X_S),
                                      2 => New_Term (Name => Y_S))),
                              Right => New_Term ("false")),
                         Right => False_Pred)));
         begin
            New_Axiom
               (File => File,
                Name => New_Bool_Int_Axiom (Rel_Symbol),
                Axiom_Body => Axiom_Body);
         end;
      end loop;
   end Declare_Boolean_Integer_Comparison;
end Why.Gen.Ints;
