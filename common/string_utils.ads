------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Uintp;                      use Uintp;

package String_Utils is
   package String_Lists is new
     Ada.Containers.Indefinite_Doubly_Linked_Lists (String);

   function Ends_With (Str, Suffix : String) return Boolean;
   --  return True when Str ends with Suffix

   function Starts_With (Str, Prefix : String) return Boolean;
   --  Check if Str starts with Prefix

   function Capitalize_First (S : String) return String;
   --  Return a string with first character capitalized

   procedure Capitalize_First (S : in out String);
   --  Modify S in place to capitalize the first character

   function Int_Image (N : Integer) return String;
   --  Generate a string from an Integer, without the leading space.

   function Uint_Image (U : Uint) return String;

   function Is_Blank (C : Character) return Boolean;
   --  Determines if C is a blank (space or tab)

   function Is_Blank (S : String) return Boolean;
   --  Determines if S has only blank characters (space or tab)

end String_Utils;
