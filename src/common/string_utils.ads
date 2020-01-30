------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Strings.Fixed;
with Ada.Containers;
with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Ada.Containers.Indefinite_Hashed_Sets;
with Ada.Strings.Hash;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with GNAT.Strings;          use GNAT.Strings;

package String_Utils is

   package String_Lists is new
     Ada.Containers.Indefinite_Doubly_Linked_Lists (String);

   use type String_Lists.Cursor;

   package String_Sets is new
     Ada.Containers.Indefinite_Hashed_Sets
       (Element_Type        => String,
        Hash                => Ada.Strings.Hash,
        Equivalent_Elements => "=",
        "="                 => "="
       );

   function Capitalize_First (S : String) return String;
   --  Return a string with first character capitalized

   procedure Capitalize_First (S : in out String);
   --  Modify S in place to capitalize the first character

   procedure Lower_Case_First (S : in out String);
   --  Modify S in place to capitalize the first character

   function Lower_Case_First (S : String) return String;

   function Standard_Ada_Case (S : String) return String;
   --  Return a string with standard Ada case, where each word separated by an
   --  underscore is capitalized.

   function Hash_Image (N : Ada.Containers.Hash_Type) return String;
   --  Generate a string from a hash, without the leading space

   function Null_Or_Empty_String (S : GNAT.Strings.String_Access)
                                  return Boolean
   is
     (S = null or else S.all = "");
   --  Return True iff S is null or the empty string

   function To_Unbounded_String (X : Boolean) return Unbounded_String is
     (To_Unbounded_String (if X then "True" else "False"));
   --  Function to print booleans

   function Trimi (S : String; C : Character) return String;
   --  Return a copy of S with all occurences of C removed

   function Case_Insensitive_Find (SL : String_Lists.List; Item : String)
                                   return String_Lists.Cursor;
   --  @param SL a list of strings
   --  @param Item a string to be found in the list
   --  @return True if a String S is in the list SL which is equal modulo
   --    casing to Item

   function Case_Insensitive_Contains (SL : String_Lists.List; Item : String)
                                       return Boolean is
     (Case_Insensitive_Find (SL, Item) /= String_Lists.No_Element);

   function Contains (S, Sub : String) return Boolean is
     (Ada.Strings.Fixed.Index (Source => S, Pattern => Sub) /= 0)
   with Pre => Sub /= "";
   --  Returns True iff string S contains substring Sub

end String_Utils;
