------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - E N U M S                         --
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

with Uintp;              use Uintp;
with Types;              use Types;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Funcs;      use Why.Gen.Funcs;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Types;      use Why.Gen.Types;
with Why.Unchecked_Ids;  use Why.Unchecked_Ids;

package body Why.Gen.Enums is

   procedure Define_Enum_To_Int_Function
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List);

   -----------------------------------
   -- Declare_Abstract_Boolean_Type --
   -----------------------------------

   procedure Declare_Abstract_Boolean_Type (File : W_File_Id; Name : String)
   is
      T : constant W_Type_Id := Declare_Abstract_Type (Name);
      --  ??? Not fully implemented yet
   begin
      File_Append_To_Declarations (File, New_Logic_Declaration (Decl => T));
   end Declare_Abstract_Boolean_Type;

   ---------------------------------
   -- Define_Enum_To_Int_Function --
   ---------------------------------

   procedure Define_Enum_To_Int_Function
      (File         : W_File_Id;
       Name         : String;
       Constructors : String_Lists.List)
      --  define conversion function from enum type to integer
      --  using pattern matching
      --  ??? Not fully implemented yet
   is
      use String_Lists;

      Arg_Name : constant String := "x";
      Func     : constant W_Function_Unchecked_Id := New_Unchecked_Function;
      Match    : constant W_Matching_Term_Unchecked_Id :=
                   New_Unchecked_Matching_Term;
      Cur      : Cursor := First (Constructors);
      Cnt      : Uint := Uint_1;
   begin
      Function_Set_Name (Func, New_Conversion_To_Int (Name));
      Function_Set_Return_Type (Func, New_Type_Int);
      Function_Append_To_Binders
        (Func,
         New_Logic_Binder
         (Name => New_Identifier (Arg_Name),
          Param_Type => New_Abstract_Type (Name)));
      Matching_Term_Set_Term (Match, New_Term (Arg_Name));
      while Has_Element (Cur) loop
         declare
            Result : constant W_Term_Id := New_Integer_Constant (Value => Cnt);
            Pat    : constant W_Pattern_Id :=
                       New_Pattern (Constr => New_Identifier (Element (Cur)));
         begin
            Matching_Term_Append_To_Branches
              (Match,
               New_Match_Case (Pattern => Pat, Term => Result));
            Cur := Next (Cur);
            Cnt := Cnt + Uint_1;
         end;
      end loop;
      Function_Set_Def (Func, Match);
      File_Append_To_Declarations
        (File,
         New_Logic_Declaration (Decl => Func));
   end Define_Enum_To_Int_Function;

   -----------------------
   -- Declare_Enum_Type --
   -----------------------

   procedure Declare_Enum_Type
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List)
   is
      --  ??? Not fully implemented yet
   begin
      File_Append_To_Declarations
        (File,
         New_Logic_Declaration
         (Decl => Declare_Enum_Type (Name, Constructors)));
      Declare_Logic (File,
                     New_Conversion_From_Int (Name),
                     (1 => New_Type_Int),
                     New_Abstract_Type (Name));
      Define_Range_Predicate
        (File,
         Name,
         First => Uint_1,
         Last => UI_From_Int (Int (String_Lists.Length (Constructors))));
      Define_Enum_To_Int_Function (File, Name, Constructors);
      Define_Coerce_Axiom
        (File,
         New_Identifier (Name),
         New_Type_Int,
         New_Conversion_From_Int (Name),
         New_Conversion_To_Int (Name));
   end Declare_Enum_Type;

end Why.Gen.Enums;
