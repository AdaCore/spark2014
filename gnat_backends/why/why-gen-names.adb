------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - N A M E S                         --
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

with Namet; use Namet;

with Why.Conversions;         use Why.Conversions;
with Why.Atree.Builders;      use Why.Atree.Builders;
with Why.Atree.Accessors;     use Why.Atree.Accessors;
with Why.Atree.Mutators;      use Why.Atree.Mutators;
with Why.Gen.Names;           use Why.Gen.Names;

package body Why.Gen.Names is

   generic
      Suffix : String;
   function Generate_Suffix (Name : String) return W_Identifier_Id;
   --  Generic for name generation functions, depending on the suffix.

   generic
      Prefix : String;
   function Generate_Prefix (Name : String) return W_Identifier_Id;
   --  Generic for name generation functions, depending on the prefix.

   --  Define all string constants that are used as suffixes.
   Array_Access       : constant String := "access";
   Array_Update       : constant String := "update";
   Array_First        : constant String := "first";
   Array_Last         : constant String := "last";
   Array_Length       : constant String := "length";
   Array_Accupd_Eq    : constant String := "accupd_eq";
   Array_Accupd_Neq   : constant String := "accupd_neq";
   Array_First_Upd    : constant String := "first_update";
   Array_Last_Upd     : constant String := "last_update";
   Array_Len_Upd      : constant String := "length_update";
   Array_Len_Nzero    : constant String := "length_non_zero";
   Array_Len_Zero     : constant String := "length_zero";
   Coerce             : constant String := "coerce";
   Boolean_Eq         : constant String := "eq_bool";
   Eq_Pred            : constant String := "eq";
   Record_Get         : constant String := "get";
   Record_Get_Axiom   : constant String := "getter";
   Record_Make        : constant String := "make";
   Of_Int             : constant String := "of_int";
   Int_Of             : constant String := "to_int";
   Definition         : constant String := "def";
   Logic_Def          : constant String := "logic";
   Logic_Def_Axiom    : constant String := "logic_def_axiom";
   Pre_Check          : constant String := "pre_check";
   Range_Name         : constant String := "range";
   In_Range           : constant String := "in_range";
   Unicity            : constant String := "unicity";

   ---------------------
   -- Generate_Prefix --
   ---------------------

   function Generate_Prefix (Name : String) return W_Identifier_Id
   is
   begin
      return New_Identifier (Prefix & "___" & Name);
   end Generate_Prefix;

   ---------------------
   -- Generate_Suffix --
   ---------------------

   function Generate_Suffix (Name : String) return W_Identifier_Id
   is
   begin
      return New_Identifier (Name & "___" & Suffix);
   end Generate_Suffix;

   function Bool_Int_Cmp_String (Rel : W_Relation) return String;
   --  Return the name of a boolean integer comparison operator

   function Array_Access_Name_Gen is new Generate_Suffix (Array_Access);
   function Array_Access_Name (Name : String) return W_Identifier_Id
      renames Array_Access_Name_Gen;

   function Array_Accupd_Eq_Gen is new Generate_Suffix (Array_Accupd_Eq);
   function Array_Accupd_Eq_Axiom (Name : String) return W_Identifier_Id
      renames Array_Accupd_Eq_Gen;

   function Array_Accupd_Neq_Gen is new Generate_Suffix (Array_Accupd_Neq);
   function Array_Accupd_Neq_Axiom (Name : String) return W_Identifier_Id
      renames Array_Accupd_Neq_Gen;

   function Array_First_Gen is new Generate_Suffix (Array_First);
   function Array_First_Name (Name : String) return W_Identifier_Id
      renames Array_First_Gen;

   function Array_First_Update_Gen is new Generate_Suffix (Array_First_Upd);
   function Array_First_Update (Name : String) return W_Identifier_Id
      renames Array_First_Update_Gen;

   function Array_Last_Gen is new Generate_Suffix (Array_Last);
   function Array_Last_Name (Name : String) return W_Identifier_Id
      renames Array_Last_Gen;

   function Array_Last_Update_Gen is new Generate_Suffix (Array_Last_Upd);
   function Array_Last_Update (Name : String) return W_Identifier_Id
      renames Array_Last_Update_Gen;

   function Array_Length_Gen is new Generate_Suffix (Array_Length);
   function Array_Length_Name (Name : String) return W_Identifier_Id
      renames Array_Length_Gen;

   function Array_Len_Nzero_Gen is new Generate_Suffix (Array_Len_Nzero);
   function Array_Length_Non_Zero (Name : String) return W_Identifier_Id
      renames Array_Len_Nzero_Gen;

   function Array_Len_Upd_Gen is new Generate_Suffix (Array_Len_Upd);
   function Array_Length_Update (Name : String) return W_Identifier_Id
      renames Array_Len_Upd_Gen;

   function Array_Len_Zero_Gen is new Generate_Suffix (Array_Len_Zero);
   function Array_Length_Zero (Name : String) return W_Identifier_Id
      renames Array_Len_Zero_Gen;

   function Array_Update_Gen is new Generate_Suffix (Array_Update);
   function Array_Update_Name (Name : String) return W_Identifier_Id
      renames Array_Update_Gen;

   -------------------------
   -- Bool_Int_Cmp_String --
   -------------------------

   function Bool_Int_Cmp_String (Rel : W_Relation) return String
   is
   begin
      case Rel is
         when W_Rel_Eq =>
            return "bool_int__eq";
         when W_Rel_Ne =>
            return "bool_int__ne";
         when W_Rel_Lt =>
            return "bool_int__lt";
         when W_Rel_Le =>
            return "bool_int__le";
         when W_Rel_Gt =>
            return "bool_int__gt";
         when W_Rel_Ge =>
            return "bool_int__ge";
      end case;
   end Bool_Int_Cmp_String;

   ------------------
   -- Coerce_Axiom --
   ------------------

   function Coerce_Gen is new Generate_Suffix (Coerce);
   function Coerce_Axiom (Name : String) return  W_Identifier_Id
      renames Coerce_Gen;

   function Coerce_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Coerce_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Coerce_Axiom;

   ------------------
   -- Eq_Param_Name --
   ------------------

   function Eq_Param_Gen is new Generate_Suffix (Boolean_Eq);
   function Eq_Param_Name (Name : String) return W_Identifier_Id
      renames Eq_Param_Gen;

   function Eq_Param_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Eq_Param_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Eq_Param_Name;

   ------------------
   -- Eq_Pred_Name --
   ------------------

   function Eq_Pred_Gen is new Generate_Suffix (Eq_Pred);
   function Eq_Pred_Name (Name : String) return W_Identifier_Id
      renames Eq_Pred_Gen;

   function Eq_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Eq_Pred_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Eq_Pred_Name;

   ----------------------
   -- New_Bool_Int_Cmp --
   ----------------------

   function New_Bool_Int_Cmp (Rel : W_Relation) return W_Identifier_Id is
   begin
      return New_Identifier (Bool_Int_Cmp_String (Rel));
   end New_Bool_Int_Cmp;

   ------------------------
   -- New_Bool_Int_Axiom --
   ------------------------

   function New_Bool_Int_Axiom (Rel : W_Relation) return W_Identifier_Id is
   begin
      return New_Identifier (Bool_Int_Cmp_String (Rel) & "_axiom");
   end New_Bool_Int_Axiom;

   --------------------------
   -- New_Conversion_Axiom --
   --------------------------

   function New_Conversion_Axiom (From : String; To : String)
      return W_Identifier_Id
   is
   begin
      return New_Identifier (To & "__of__" & From & "__in_range");
   end New_Conversion_Axiom;

   function Of_Int_Gen is new Generate_Suffix (Of_Int);
   function New_Conversion_From_Int (Name : String) return W_Identifier_Id
      renames Of_Int_Gen;

   function Int_Of_Gen is new Generate_Suffix (Int_Of);
   function New_Conversion_To_Int (Name : String) return W_Identifier_Id
      renames Int_Of_Gen;

   function Definition_Gen is new Generate_Prefix (Definition);
   function New_Definition_Name (Name : String) return W_Identifier_Id
      renames Definition_Gen;

   function Logic_Def_Gen is new Generate_Prefix (Logic_Def);
   function Logic_Func_Name (Name : String) return W_Identifier_Id
      renames Logic_Def_Gen;

   function Logic_Def_Axiom_Gen is new Generate_Suffix (Logic_Def_Axiom);
   function Logic_Func_Axiom (Name : String) return W_Identifier_Id
      renames Logic_Def_Axiom_Gen;

   function Pre_Check_Gen is new Generate_Prefix (Pre_Check);
   function New_Pre_Check_Name (Name : String) return W_Identifier_Id
      renames Pre_Check_Gen;

   -------------------------
   -- New_Exit_Identifier --
   -------------------------

   function New_Exit_Identifier return W_Identifier_Id is
      Exit_Name : constant String := "Exit";
   begin
      return New_Identifier (Exit_Name);
   end New_Exit_Identifier;

   --------------------
   -- New_Identifier --
   --------------------

   function New_Identifier (Name : String) return W_Identifier_Id is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      return New_Identifier (Symbol => Name_Find);
   end New_Identifier;

   ---------------------
   -- New_Identifiers --
   ---------------------

   function New_Identifiers
     (SL : String_Lists.List) return W_Identifier_Array is
      use String_Utils.String_Lists;

      Result : W_Identifier_Array (1 .. Integer (Length (SL)));
      Index  : Positive := 1;
   begin
      --  Workaround for K526-008 and K525-019

      --  for E of SL loop
      --     Result (Index) := New_Identifier (E);
      --     Index := Index + 1;
      --  end loop;

      declare
         C : Cursor := SL.First;
      begin
         while C /= No_Element loop
            Result (Index) := New_Identifier (Element (C));
            Index := Index + 1;
            Next (C);
         end loop;
      end;
      return Result;
   end New_Identifiers;

   ---------------------
   -- New_Ignore_Name --
   ---------------------

   function New_Ignore_Name return W_Identifier_Id
   is
   begin
      return New_Identifier ("___ignore");
   end New_Ignore_Name;

   --------------------------
   -- New_Integer_Division --
   --------------------------

   function New_Integer_Division return W_Identifier_Id is
      Name : constant String := "computer_div";
   begin
      return New_Identifier (Name);
   end New_Integer_Division;

   ---------------------------
   -- New_Result_Identifier --
   ---------------------------

   function New_Result_Identifier return W_Identifier_Id is
      Result_Name : constant String := "result";
   begin
      return New_Identifier (Result_Name);
   end New_Result_Identifier;

   -------------------------------
   -- New_Result_Exc_Identifier --
   -------------------------------

   function New_Result_Exc_Identifier return W_Identifier_Id is
      Result_Name : constant String := "_result_exc";
   begin
      return New_Identifier (Result_Name);
   end New_Result_Exc_Identifier;

   --------------------------------
   -- New_Result_Temp_Identifier --
   --------------------------------

   function New_Result_Temp_Identifier return W_Identifier_Id is
      Result_Name : constant String := "_result";
   begin
      return New_Identifier (Result_Name);
   end New_Result_Temp_Identifier;

   --------------
   -- New_Term --
   --------------

   function New_Term (Name : String) return W_Term_Id is
   begin
      return New_Term_Identifier (Name => New_Identifier (Name));
   end New_Term;

   ---------------
   -- New_Terms --
   ---------------

   function New_Terms (SL : String_Lists.List) return W_Term_Array is
      use String_Utils.String_Lists;

      Result : W_Term_Array (1 .. Integer (Length (SL)));
      Index  : Positive := 1;
   begin
      --  Workaround for K526-008 and K525-019

      --  for E of SL loop
      --     Result (Index) := New_Term (E);
      --     Index := Index + 1;
      --  end loop;

      declare
         C : Cursor := SL.First;
      begin
         while C /= No_Element loop
            Result (Index) := New_Term (Element (C));
            Index := Index + 1;
            Next (C);
         end loop;
      end;

      return Result;
   end New_Terms;

   -----------------
   -- Range_Axiom --
   -----------------

   function Range_Axiom_Gen is new Generate_Suffix (Range_Name);
   function Range_Axiom (Name : String) return  W_Identifier_Id
      renames Range_Axiom_Gen;

   function Range_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Range_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Range_Axiom;

   function In_Range_Gen is new Generate_Suffix (In_Range);
   function Range_Pred_Name (Name : String) return W_Identifier_Id
      renames In_Range_Gen;

   function Range_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Range_Pred_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Range_Pred_Name;

   -------------------------
   -- Record_Builder_Name --
   -------------------------

   function Record_Builder_Name_Gen is new Generate_Prefix (Record_Make);
   function Record_Builder_Name (Name : String) return W_Identifier_Id
      renames Record_Builder_Name_Gen;

   function Record_Builder_Name (Name : W_Identifier_Id) return W_Identifier_Id
   is
   begin
      return Record_Builder_Name
        (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Record_Builder_Name;

   -------------------------
   -- Record_Getter_Axiom --
   -------------------------

   function Record_Getter_Axiom_Gen is
     new Generate_Suffix (Record_Get_Axiom);
   function Record_Getter_Axiom (Name : String) return W_Identifier_Id
     renames Record_Getter_Axiom_Gen;

   -------------------------
   -- Record_Getter_Name --
   -------------------------

   function Record_Getter_Name_Gen is new Generate_Prefix (Record_Get);
   function Record_Getter_Name (Name : String) return W_Identifier_Id
     renames Record_Getter_Name_Gen;

   function Record_Getter_Name (Name : W_Identifier_Id) return W_Identifier_Id
   is
   begin
      return Record_Getter_Name
        (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Record_Getter_Name;

   --------------
   -- Set_Name --
   --------------

   procedure Set_Name (Id : W_Identifier_Id; Name : String) is
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Name);
      Identifier_Set_Symbol (Id, Name_Find);
   end Set_Name;

   ----------------------
   -- To_Program_Space --
   ----------------------

   function To_Program_Space (Name : W_Identifier_Id) return W_Identifier_Id is
      Suffix : constant String := "_";
      N_Id   : constant Name_Id := Identifier_Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier (Img & Suffix);
   end To_Program_Space;

   -------------------------
   -- To_Label_Identifier --
   -------------------------

   function To_Term_Identifier
     (Name : W_Identifier_Id)
     return W_Term_Id is
   begin
      return New_Term_Identifier (Name => +Duplicate_Any_Node (Id => +Name));
   end To_Term_Identifier;

   -------------------
   -- Unicity_Axiom --
   -------------------

   function Unicity_Gen is new Generate_Suffix (Unicity);
   function Unicity_Axiom (Name : String) return  W_Identifier_Id
      renames Unicity_Gen;

   function Unicity_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Unicity_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Unicity_Axiom;

end Why.Gen.Names;
