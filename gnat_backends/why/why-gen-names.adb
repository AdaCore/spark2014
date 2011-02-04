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

with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;

package body Why.Gen.Names is

   --------------------
   -- Allocator_Name --
   --------------------

   function Allocator_Name (Name : String) return W_Identifier_Id is
      Prefix : constant String := "any___";
   begin
      return New_Identifier (Prefix & Name);
   end Allocator_Name;

   -----------------------
   -- Array_Access_Name --
   -----------------------

   function Array_Access_Name (Name : String) return W_Identifier_Id
   is
      Suffix : constant String := "__access";
   begin
      return New_Identifier (Name & Suffix);
   end Array_Access_Name;

   ---------------------------
   -- Array_Accupd_Eq_Axiom --
   ---------------------------

   function Array_Accupd_Eq_Axiom (Name : String) return W_Identifier_Id
   is
      Suffix : constant String := "__accupd_eq";
   begin
      return New_Identifier (Name & Suffix);
   end Array_Accupd_Eq_Axiom;

   -----------------------
   -- Array_Update_Name --
   -----------------------

   function Array_Update_Name (Name : String) return W_Identifier_Id
   is
      Suffix : constant String := "__update";
   begin
      return New_Identifier (Name & Suffix);
   end Array_Update_Name;

   ------------------
   -- Coerce_Axiom --
   ------------------

   function Coerce_Axiom (Name : String) return  W_Identifier_Id is
      Suffix : constant String := "___coerce";
   begin
      return New_Identifier (Name & Suffix);
   end Coerce_Axiom;

   function Coerce_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Coerce_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Coerce_Axiom;

   ------------------
   -- Eq_Param_Name --
   ------------------

   function Eq_Param_Name (Name : String) return W_Identifier_Id is
      Prefix : constant String := "eq_bool___";
   begin
      return New_Identifier (Prefix & Name);
   end Eq_Param_Name;

   function Eq_Param_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Eq_Param_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Eq_Param_Name;

   ------------------
   -- Eq_Pred_Name --
   ------------------

   function Eq_Pred_Name (Name : String) return W_Identifier_Id is
      Prefix : constant String := "eq___";
   begin
      return New_Identifier (Prefix & Name);
   end Eq_Pred_Name;

   function Eq_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Eq_Pred_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Eq_Pred_Name;

   --------------------------
   -- New_Conversion_Axiom --
   --------------------------

   function New_Conversion_Axiom (From : String; To : String)
      return W_Identifier_Id
   is
   begin
      return New_Identifier (To & "__of__" & From & "__in_range");
   end New_Conversion_Axiom;

   -----------------------------
   -- New_Conversion_From_Int --
   -----------------------------

   function New_Conversion_From_Int (Name : String) return W_Identifier_Id is
      Suffix : constant String := "___of_int";
   begin
      return New_Identifier (Name & Suffix);
   end New_Conversion_From_Int;

   ---------------------------
   -- New_Conversion_To_Int --
   ---------------------------

   function New_Conversion_To_Int (Name : String) return W_Identifier_Id is
      Prefix : constant String := "int_of___";
   begin
      return New_Identifier (Prefix & Name);
   end New_Conversion_To_Int;

   -------------------------
   -- New_Definition_Name --
   -------------------------

   function New_Definition_Name (Name : String) return String is
      Prefix : constant String  := "def___";
   begin
      return Prefix & Name;
   end New_Definition_Name;

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

   ---------------------------
   -- New_Result_Identifier --
   ---------------------------

   function New_Result_Identifier return W_Identifier_Id is
      Result_Name : constant String := "result";
   begin
      return New_Term_Identifier (Name => New_Identifier (Result_Name));
   end New_Result_Identifier;

   --------------
   -- New_Term --
   --------------

   function New_Term (Name : String) return W_Term_Identifier_Id is
   begin
      return New_Term_Identifier (Name => New_Identifier (Name));
   end New_Term;

   -----------------
   -- Range_Axiom --
   -----------------

   function Range_Axiom (Name : String) return  W_Identifier_Id is
      Suffix : constant String := "___range";
   begin
      return New_Identifier (Name & Suffix);
   end Range_Axiom;

   function Range_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Range_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Range_Axiom;

   ---------------------
   -- Range_Pred_Name --
   ---------------------

   function Range_Pred_Name (Name : String) return W_Identifier_Id is
      Suffix : constant String := "___in_range";
   begin
      return New_Identifier (Name & Suffix);
   end Range_Pred_Name;

   function Range_Pred_Name (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Range_Pred_Name (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Range_Pred_Name;

   ------------------
   -- Safe_Version --
   ------------------

   function Safe_Version (Name : W_Identifier_Id) return W_Identifier_Id is
      Prefix : constant String := "safe___";
      N_Id   : constant Name_Id := Identifier_Get_Symbol (Name);
      Img    : constant String := Get_Name_String (N_Id);
   begin
      return New_Identifier (Prefix & Img);
   end Safe_Version;

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
     return W_Term_Identifier_Id is
   begin
      return New_Term_Identifier (Name => Duplicate_Any_Node (Id => Name));
   end To_Term_Identifier;

   -------------------
   -- Unicity_Axiom --
   -------------------

   function Unicity_Axiom (Name : String) return  W_Identifier_Id is
      Suffix : constant String := "___unicity";
   begin
      return New_Identifier (Name & Suffix);
   end Unicity_Axiom;

   function Unicity_Axiom (Name : W_Identifier_Id) return W_Identifier_Id is
   begin
      return Unicity_Axiom (Get_Name_String (Identifier_Get_Symbol (Name)));
   end Unicity_Axiom;

end Why.Gen.Names;
