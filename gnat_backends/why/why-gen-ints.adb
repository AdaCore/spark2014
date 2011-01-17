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
with Why.Gen.Types;      use Why.Gen.Types;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Funcs;      use Why.Gen.Funcs;
with Why.Gen.Arrows;     use Why.Gen.Arrows;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Axioms;     use Why.Gen.Axioms;

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
      T : constant W_Type_Id := New_Abstract_Type_Declaration (Name);
   begin
      File_Append_To_Declarations (File, New_Logic_Declaration (Decl => T));
      Declare_Allocator (File, Name);
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
      Declare_Logic (File,
                     New_Conversion_To_Int (Name),
                     (1 => New_Abstract_Type (Name)),
                     New_Type_Int);

      --  from int:
      declare
         Return_Type : constant W_Primitive_Type_Id :=
                         New_Abstract_Type (Name);
         Arrows      : W_Arrow_Type_Unchecked_Id :=
                         New_Arrow_Stack (Return_Type);
         --  precondition: { <name>___in_range (n) }
         Range_Check : constant W_Operation_Id :=
                         New_Operation (Name =>
                                          Range_Pred_Name (Name),
                                        Parameters =>
                                          (1 => New_Term (Arg_S)));
         --  postcondition: { <name>___of_integer (result) = n }
         Int_Result  : constant W_Operation_Id :=
                         New_Operation (Name =>
                                          New_Conversion_To_Int (Name),
                                        Parameters =>
                                          (1 => New_Result_Identifier));
         Post        : constant W_Predicate_Id :=
                         New_Related_Terms (Left  => Int_Result,
                                            Op    => New_Rel_Eq,
                                            Right => New_Term (Arg_S));
      begin
         Arrows := Push_Arg (Arrows, New_Identifier (Arg_S), New_Type_Int);

         Declare_Logic_And_Parameters (File,
                                       New_Conversion_From_Int (Name),
                                       Arrows,
                                       Range_Check,
                                       Post);
         Define_Eq_Predicate (File, Name);
         Define_Range_Axiom (File,
                             New_Identifier (Name),
                             New_Conversion_To_Int (Name));
         Define_Coerce_Axiom (File,
                              New_Identifier (Name),
                              New_Type_Int,
                              New_Conversion_From_Int (Name),
                              New_Conversion_To_Int (Name));
         Define_Unicity_Axiom (File,
                               New_Identifier (Name),
                               New_Conversion_To_Int (Name));
      end;
   end Define_Signed_Int_Conversions;

end Why.Gen.Ints;
