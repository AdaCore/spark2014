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

end Sparkify.Names;
