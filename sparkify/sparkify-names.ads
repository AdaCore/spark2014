------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                        S P A R K I F Y . N A M E S                       --
--                                                                          --
--                                 S p e c                                  --
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

--  This package provides comparison of strings that ignores case and
--  surrounding white space

with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;
with Ada.Containers.Hashed_Sets;
with Ada.Containers;                   use Ada.Containers;

package Sparkify.Names is

   type Name_String is new Unbounded_Wide_String;
   --  This type abstracts names so that testing equality is performed modulo
   --  the case

   --  All literals in the following constant definitions of type Name_String
   --  should be in lowercase

   procedure Initialize;

   function Normalized_Name (Str : Wide_String) return Name_String;
   --  If the argument string Str consists only of characters which
   --  belong to the first 256 positions of Wide_Character type, it returns
   --  this word converted to lower case characters, with surrounding white
   --  space removed. Otherwise it returns this word as it is.

   function Lit (Str : Wide_String) return Name_String renames Normalized_Name;

   function Length (N : Name_String) return Natural;

   Nil_Name                  : Name_String;
   Precondition_Name         : Name_String;
   Postcondition_Name        : Name_String;
   Check_Name                : Name_String;
   Old_Name                  : Name_String;
   Result_Name               : Name_String;

   Old_Length                : Natural;
   Result_Length             : Natural;

   Check_Position_In_Assert  : Natural     := 0;
   Check_Position_In_Prepost : Natural     := 0;

   function "=" (Str : Wide_String; Name : Name_String) return Boolean;
   --  Tests the equality between a string extracted from the program text and
   --  a name, performing the appropriate conversion on Str to ignore case and
   --  removing surrounding white space

   function Hash (Element : Name_String) return Hash_Type;

   function Equivalent_Elements (Left, Right : Name_String) return Boolean;

   function "=" (Left, Right : Name_String) return Boolean
      renames Equivalent_Elements;

   package Nameset is new Hashed_Sets (Name_String, Hash, Equivalent_Elements);

   function Concat_Names (Container : Nameset.Set;
                          Separator : Wide_String) return Wide_String;

end Sparkify.Names;
