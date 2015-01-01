------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Handling;

package body String_Utils is

   ---------------
   -- Ends_With --
   ---------------

   function Ends_With (Str, Suffix : String) return Boolean
   is
   begin
      if Suffix'Length > Str'Length then
         return False;
      end if;
      for Index in reverse Suffix'First .. Suffix'Last loop
         if Str (Str'Last - Suffix'Last + Index) /= Suffix (Index) then
            return False;
         end if;
      end loop;
      return True;
   end Ends_With;

   ----------------------
   -- Capitalize_First --
   ----------------------

   function Capitalize_First (S : String) return String is
      T : String := S;
   begin
      Capitalize_First (T);
      return T;
   end Capitalize_First;

   procedure Capitalize_First (S : in out String) is
   begin
      S (S'First) := Ada.Characters.Handling.To_Upper (S (S'First));
   end Capitalize_First;

   ----------------
   -- Hash_Image --
   ----------------

   function Hash_Image (N : Ada.Containers.Hash_Type) return String is
      Result : constant String := Ada.Containers.Hash_Type'Image (N);
   begin
      return Result (Result'First + 1 .. Result'Last);
   end Hash_Image;

   ---------------
   -- Int_Image --
   ---------------

   function Int_Image (N : Integer) return String is
      Result : constant String := Integer'Image (N);
   begin
      if N >= 0 then
         return Result (Result'First + 1 .. Result'Last);
      else
         return Result;
      end if;
   end Int_Image;

   --------------
   -- Is_Blank --
   --------------

   function Is_Blank (C : Character) return Boolean is
   begin
      return C = ' ' or else C = ASCII.HT;
   end Is_Blank;

   function Is_Blank (S : String) return Boolean is
   begin
      return (for all J in S'Range => Is_Blank (S (J)));
   end Is_Blank;

   ----------------------
   -- Lower_Case_First --
   ----------------------

   procedure Lower_Case_First (S : in out String)
   is
   begin
      S (S'First) := Ada.Characters.Handling.To_Lower (S (S'First));
   end Lower_Case_First;

   -----------------
   -- Starts_With --
   -----------------

   function Starts_With (Str, Prefix : String) return Boolean is
   begin
      if Str'Length < Prefix'Length then
         return False;
      end if;
      for Index in Prefix'Range loop
         if Str (Str'First + Index - Prefix'First) /= Prefix (Index) then
            return False;
         end if;
      end loop;
      return True;
   end Starts_With;

end String_Utils;
