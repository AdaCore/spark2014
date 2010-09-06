------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                U T I L S                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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

with Ada.Strings.Wide_Fixed;     use Ada.Strings.Wide_Fixed;
with Asis.Text;                  use Asis.Text;
with Ada.Strings;                use Ada.Strings;

package body Utils is

   ---------
   -- Img --
   ---------

   function Img (Element : Asis.Element) return Wide_String is
   begin
      return Trim (Asis.Text.Element_Image (Element), Both);
   end Img;

   ------------------
   -- Strip_Prefix --
   ------------------

   function Strip_Prefix (Name : Wide_String) return Wide_String is
      Start : Integer := Name'First;
   begin
      for J in Name'Range loop
         if Name (J) = '_' then
            Start := J + 1;
            exit;
         end if;
      end loop;

      return Name (Start .. Name'Last);
   end Strip_Prefix;

   ------------------
   -- Strip_Suffix --
   ------------------

   function Strip_Suffix (Name : Wide_String) return Wide_String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J - 1;
            exit;
         end if;
      end loop;

      return Name (Name'First .. Stop);
   end Strip_Suffix;

   ------------
   -- Suffix --
   ------------

   function Suffix (Name : Wide_String) return Wide_String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J;
            exit;
         end if;
      end loop;

      return Name (Stop + 1 .. Name'Last);
   end Suffix;

end Utils;
