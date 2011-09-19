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

with Ada.Containers;     use Ada.Containers;
with Uintp;              use Uintp;
with Types;              use Types;
with Why.Sinfo;          use Why.Sinfo;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Atree.Mutators; use Why.Atree.Mutators;
with Why.Gen.Axioms;     use Why.Gen.Axioms;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Funcs;      use Why.Gen.Funcs;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Preds;      use Why.Gen.Preds;
with Why.Gen.Terms;      use Why.Gen.Terms;
with Why.Gen.Types;      use Why.Gen.Types;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Consts;     use Why.Gen.Consts;
with Why.Unchecked_Ids;  use Why.Unchecked_Ids;

package body Why.Gen.Enums is

   function P (Id : W_Expr_OId) return W_Prog_OId renames "+";

   procedure Define_Enum_To_Int_Function
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List);
   --  define conversion function from enum type to integer
   --  using pattern matching
   --  example: for a type definition
   --     type T is (A, B, C)
   --  define a Why function
   --    function t__to_integer (x : t) =
   --     match x with
   --     | a -> 1
   --     | b -> 2
   --     | c -> 3

   ---------------------------------
   -- Define_Enum_To_Int_Function --
   ---------------------------------

   procedure Define_Enum_To_Int_Function
      (File         : W_File_Id;
       Name         : String;
       Constructors : String_Lists.List)
      --  ??? Not fully implemented yet
   is
      use String_Lists;

      Arg_Name : constant String := "x";
      Match    : constant W_Match_Unchecked_Id :=
                   New_Unchecked_Match;
      Cur      : Cursor := First (Constructors);
      Cnt      : Uint := Uint_1;
   begin
      Match_Set_Term (Match, New_Term (Arg_Name));
      while Has_Element (Cur) loop
         declare
            Result : constant W_Term_Id := New_Integer_Constant (Value => Cnt);
            Pat    : constant W_Pattern_Id :=
                       New_Pattern
                         (Constr => New_Identifier (Element (Cur)));
         begin
            Match_Append_To_Branches
              (Match,
               New_Match_Case (Pattern => Pat, Term => Result));
            Cur := Next (Cur);
            Cnt := Cnt + Uint_1;
         end;
      end loop;

      declare
         Func : constant W_Declaration_Id :=
                  New_Function_Def
                    (Domain      => EW_Term,
                     Name        => Conversion_To.Id (Name, "int"),
                     Return_Type => New_Base_Type (Base_Type => EW_Int),
                     Binders     =>
                       (1 =>
                          (B_Name =>
                             New_Identifier
                               (Domain => EW_Term,
                                Name   => Arg_Name),
                           B_Type =>
                             New_Abstract_Type
                               (Name => New_Identifier (Name)),
                           others => <>)),
                     Def         => +Match);
      begin
         Emit (File, Func);
      end;
   end Define_Enum_To_Int_Function;

   ---------------------------
   -- Declare_Ada_Enum_Type --
   ---------------------------

   procedure Declare_Ada_Enum_Type
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List)
   is
      Len      : constant Count_Type := String_Lists.Length (Constructors);
      My_Type  : constant W_Primitive_Type_Id :=
                   New_Abstract_Type
                     (Name => New_Identifier (Name));
      Max_Uint : constant Uint := UI_From_Int (Int (Len));
   begin
      pragma Assert (Len > 0);
      New_Enum_Type_Declaration (File, Name, Constructors);
      Emit
        (File,
         Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        =>
              Conversion_From.Id (Name, "int"),
            Binders     =>
              New_Binders ((1 => New_Base_Type (Base_Type => EW_Int))),
            Return_Type => My_Type));
      Define_Enum_To_Int_Function (File, Name, Constructors);
      Define_Range_Predicate
        (File,
         Name,
         EW_Int,
         First => New_Constant (Uint_1),
         Last  => New_Constant (Max_Uint));
      Emit
        (File,
         New_Function_Decl
           (Domain      => EW_Prog,
            Name        => To_Program_Space (Conversion_From.Id (Name, "int")),
            Binders     =>
              (1 =>
                 (B_Name => New_Identifier ("x"),
                  B_Type => New_Base_Type (Base_Type => EW_Int),
                  others => <>)),
            Return_Type => My_Type,
            Pre         =>
              New_Relation
                (Op_Type => EW_Int,
                 Left    => New_Integer_Constant (Value => Uint_1),
                 Op      => EW_Le,
                 Right   => +New_Term ("x"),
                 Op2     => EW_Le,
                 Right2  => New_Integer_Constant (Value => Max_Uint)),
            Post        =>
              New_Relation
                (Op_Type => EW_Int,
                 Op      => EW_Eq,
                 Left    => +New_Result_Term,
                 Right   =>
                   P (New_Call
                     (Domain => EW_Term,
                      Name   => Conversion_From.Id (Name, "int"),
                      Args   => (1 => +New_Term ("x")))))));
      Define_Coerce_Axiom
        (File,
         New_Identifier (Name),
         EW_Int);
      New_Boolean_Equality_Parameter (File, Name);
   end Declare_Ada_Enum_Type;

end Why.Gen.Enums;
