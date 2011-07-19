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

with Namet;               use Namet;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Gen.Names;       use Why.Gen.Names;

package body Why.Gen.Names is

   function Bool_Int_Cmp_String (Rel : W_Relation) return String;
   --  Return the name of a boolean integer comparison operator

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

   -------------------------------
   -- New_Result_Exc_Identifier --
   -------------------------------

   function New_Result_Exc_Identifier return W_Identifier_Id is
      Result_Name : constant String := "_result_exc";
   begin
      return New_Identifier (Result_Name);
   end New_Result_Exc_Identifier;

   ---------------------------
   -- New_Result_Identifier --
   ---------------------------

   function New_Result_Identifier return W_Identifier_Id is
      Result_Name : constant String := "result";
   begin
      return New_Identifier (Result_Name);
   end New_Result_Identifier;

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

   ------------------------
   -- To_Term_Identifier --
   ------------------------

   function To_Term_Identifier
     (Name : W_Identifier_Id)
     return W_Term_Id is
   begin
      return New_Term_Identifier (Name => Name);
   end To_Term_Identifier;

end Why.Gen.Names;
