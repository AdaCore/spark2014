------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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
with GNATCOLL.Utils;        use GNATCOLL.Utils;
with GNAT.Case_Util;

package body String_Utils is

   --------------------------
   -- Capitalize_All_First --
   --------------------------

   function Capitalize_All_First (S : String) return String is
      T : String := S;
   begin
      Capitalize_All_First (T);
      return T;
   end Capitalize_All_First;

   procedure Capitalize_All_First (S : in out String) is
      Capitalize : Boolean := True;
   begin
      for J in S'Range loop
         if Capitalize then
            S (J) := Ada.Characters.Handling.To_Upper (S (J));
         end if;
         Capitalize := S (J) = '_';
      end loop;
   end Capitalize_All_First;

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

   ---------------------------
   -- Case_Insensitive_Find --
   ---------------------------

   function Case_Insensitive_Find (SL : String_Lists.List; Item : String)
                                   return String_Lists.Cursor is
      use String_Lists;
   begin
      for C in SL.Iterate loop
         if Case_Insensitive_Equal (SL (C), Item) then
            return C;
         end if;
      end loop;
      return String_Lists.No_Element;
   end Case_Insensitive_Find;

   ----------------
   -- Hash_Image --
   ----------------

   function Hash_Image (N : Ada.Containers.Hash_Type) return String is
      Result : constant String := Ada.Containers.Hash_Type'Image (N);
   begin
      return Result (Result'First + 1 .. Result'Last);
   end Hash_Image;

   ----------------------
   -- Lower_Case_First --
   ----------------------

   procedure Lower_Case_First (S : in out String) is
   begin
      S (S'First) := Ada.Characters.Handling.To_Lower (S (S'First));
   end Lower_Case_First;

   function Lower_Case_First (S : String) return String is
      T : String := S;
   begin
      Lower_Case_First (T);
      return T;
   end Lower_Case_First;

   -----------------------
   -- Standard_Ada_Case --
   -----------------------

   function Standard_Ada_Case (S : String) return String is
      T : String := S;
   begin
      GNAT.Case_Util.To_Mixed (T);
      return T;
   end Standard_Ada_Case;

   -----------
   -- Trimi --
   -----------

   function Trimi (S : String; C : Character) return String is
      R : String (1 .. S'Last);
      J : Natural := 0;
   begin
      for I of S loop
         if I /= C then
            J := J + 1;
            R (J) := I;
         end if;
      end loop;
      return R (1 .. J);
   end Trimi;

end String_Utils;
