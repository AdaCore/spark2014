------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                        S P A R K I F Y . N A M E S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Handling;          use Ada.Characters.Handling;
with Ada.Strings.Wide_Hash;
with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;
with Ada.Strings.Unbounded;            use Ada.Strings.Unbounded;
with Ada.Strings.Wide_Maps;
with Ada.Containers.Ordered_Maps;
with Sparkify.Stringset;               use Sparkify.Stringset;

with ASIS_UL.Strings;                  use ASIS_UL.Strings;
with Asis.Declarations;                use Asis.Declarations;

package body Sparkify.Names is

   ----------
   -- Init --
   ----------

   procedure Initialize is
   begin
      Nil_Name           := Lit ("");
      Precondition_Name  := Lit ("precondition");
      Postcondition_Name := Lit ("postcondition");
      Check_Name         := Lit ("check");
      Old_Name           := Lit ("old");
      Result_Name        := Lit ("result");

      Old_Length         := Length (Old_Name);
      Result_Length      := Length (Result_Name);
   end Initialize;

   -----------------------
   -- Flat_Package_Name --
   -----------------------

   function Flat_Package_Name (Str : Wide_String) return Wide_String is
      use Ada.Strings.Wide_Maps;
      Dot   : constant Wide_Character_Sequence := To_Sequence (To_Set ('.'));
      Under : constant Wide_Character_Sequence := To_Sequence (To_Set ('_'));
   begin
      return Translate (Str, To_Mapping (Dot, Under));
   end Flat_Package_Name;

   ---------------------
   -- Normalized_Name --
   ---------------------

   function Normalized_Name (Str : Wide_String) return Name_String is
      Result : Wide_String := Trim (Str, Ada.Strings.Both);
   begin

      if Is_String (Result) then
         Result := To_Wide_String (To_Lower (To_String (Result)));
      end if;

      return Name_String
        (Ada.Strings.Wide_Unbounded.To_Unbounded_Wide_String (Result));

   end Normalized_Name;

   ------------
   -- Length --
   ------------

   function Length (N : Name_String) return Natural is
   begin
      return Length (Unbounded_Wide_String (N));
   end Length;

   ---------
   -- "=" --
   ---------

   function "=" (Str : Wide_String; Name : Name_String) return Boolean is
   begin
      return Normalized_Name (Str) = Name;
   end "=";

   ----------
   -- Hash --
   ----------

   function Hash (Element : Name_String) return Hash_Type is
   begin
      return Ada.Strings.Wide_Hash
        (To_Wide_String (Unbounded_Wide_String (Element)));
   end Hash;

   -------------------------
   -- Equivalent_Elements --
   -------------------------

   function Equivalent_Elements (Left, Right : Name_String) return Boolean is
   begin
      return Unbounded_Wide_String (Left) = Unbounded_Wide_String (Right);
   end Equivalent_Elements;

   ------------------
   -- Concat_Names --
   ------------------

   function Concat_Names
     (Container : Nameset.Set;
      Separator : Wide_String) return Wide_String
   is
      Len   : Natural := 0;
      Count : Natural := 0;

      procedure Add_To_Length (Position : Nameset.Cursor);

      procedure Add_To_Length (Position : Nameset.Cursor) is
      begin
         Count := Count + 1;
         Len := Len + Length (Nameset.Element (Position)) + Separator'Length;
      end Add_To_Length;

   begin
      Nameset.Iterate (Container, Add_To_Length'Access);
      if Count /= 0 then
         Len := Len - Separator'Length;
      end if;

      declare
         Result : Wide_String (1 .. Len);
         Index : Natural := 1;

         procedure Concat_At_Index (Position : Nameset.Cursor);

         procedure Concat_At_Index (Position : Nameset.Cursor)
         is
            Element    : constant Name_String := Nameset.Element (Position);
            Sep_Index  : constant Natural := Index + Length (Element);
            Next_Index : constant Natural := Sep_Index + Separator'Length;
         begin
            Result (Index .. Sep_Index - 1) := To_Wide_String (Element);
            if Count > 1 then
               Result (Sep_Index .. Next_Index - 1) := Separator;
               Index := Next_Index;
               Count := Count - 1;
            else
               Index := Sep_Index;
            end if;
         end Concat_At_Index;

      begin
         Nameset.Iterate (Container, Concat_At_Index'Access);
         pragma Assert (Index = Len + 1);
         return Result;
      end;
   end Concat_Names;

   ----------------
   -- Fresh_Name --
   ----------------

   --  Global variable for counting the new names created
   Count_Name : Natural := 0;

   function Fresh_Name return Wide_String is
   begin
      Count_Name := Count_Name + 1;
      return "New_Name_" &
      Trim (Natural'Wide_Image (Count_Name), Ada.Strings.Left);
   end Fresh_Name;

   function Fresh_Name (New_Name : Wide_String) return Wide_String is
   begin
      Count_Name := Count_Name + 1;
      return New_Name &
      Trim (Natural'Wide_Image (Count_Name), Ada.Strings.Left);
   end Fresh_Name;

   ------------------
   -- Loc_To_Names --
   ------------------

   package Loc_To_Name_Map is new Ada.Containers.Ordered_Maps
      (Key_Type     => Unbounded_String,
       Element_Type => Unbounded_Wide_String);

   use Loc_To_Name_Map;

   Loc_To_Names : Map;

   --------------------
   -- Store_New_Name --
   --------------------

   procedure Store_New_Name
     (El   : Asis.Element;
      Name : Unbounded_Wide_String)
   is
      Loc : constant Unbounded_String :=
              To_Unbounded_String (Build_GNAT_Location (El));
   begin
      Insert (Loc_To_Names, Loc, Name);
   end Store_New_Name;

   ------------------
   -- Get_New_Name --
   ------------------

   function Get_New_Name (El : Asis.Element) return Unbounded_Wide_String is
      Loc : constant Unbounded_String :=
              To_Unbounded_String (Build_GNAT_Location (El));
      C   : constant Loc_To_Name_Map.Cursor := Find (Loc_To_Names, Loc);
   begin
      if C /= Loc_To_Name_Map.No_Element then
         return Loc_To_Name_Map.Element (C);
      else
         return To_Unbounded_Wide_String ("");
      end if;
   end Get_New_Name;

   ----------------------------
   -- Return_Overloaded_Name --
   ----------------------------

   --  To store the names of subprograms no overload
   Names : Stringset.Set;

   function Return_Overloaded_Name
     (Decl : Asis.Declaration) return Unbounded_Wide_String
   is
      Proc_Names    : constant Defining_Name_List :=
                        Asis.Declarations.Names (Decl);
      Defining_Name : Unbounded_Wide_String :=
                        To_Unbounded_Wide_String
                          (Defining_Name_Image
                             (Proc_Names (Proc_Names'First)));
      New_Name      : constant Unbounded_Wide_String := Get_New_Name (Decl);
   begin
      pragma Assert (Proc_Names'Length = 1);

      if New_Name /= "" then
         return New_Name;
      else
         if Contains (Names, Defining_Name) then
            Defining_Name := To_Unbounded_Wide_String (Fresh_Name (
              (Defining_Name_Image (Proc_Names (Proc_Names'First)))));

            Store_New_Name (Decl, Defining_Name);

            return Defining_Name;
         else
            Stringset.Insert (Container => Names,
                              New_Item  => Defining_Name);

            Store_New_Name (Decl, Defining_Name);

            return Defining_Name;
         end if;
      end if;

   end Return_Overloaded_Name;

end Sparkify.Names;
