------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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

   ----------------------
   -- Lower_Case_First --
   ----------------------

   procedure Lower_Case_First (S : in out String) is
   begin
      S (S'First) := Ada.Characters.Handling.To_Lower (S (S'First));
   end Lower_Case_First;

end String_Utils;
