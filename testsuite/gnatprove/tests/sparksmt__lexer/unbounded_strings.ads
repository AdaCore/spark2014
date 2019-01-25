------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                    U N B O U N D E D _ S T R I N G S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

private with Ada.Containers.Formal_Indefinite_Vectors;

--  A helper package for dealing with variable-length char arrays.

package Unbounded_Strings with
   SPARK_Mode
is

   type Unbounded_String is limited private
     with Default_Initial_Condition =>
       Length (Unbounded_String) = 0;

   function Length (S : Unbounded_String) return Natural
   with Global => null;
   --  The length of the current string.

   procedure New_String (S : out Unbounded_String)
   with Global => null,
        Post   => Length (S) = 0;
   --  Creats a new empty string.

   procedure Append (S : in out Unbounded_String;
                     C : Character)
   with Global => null,
        Post   => Length (S) = Length (S)'Old + 1;
   --  Add the character C to the given string.

   function To_String (S : Unbounded_String) return String
   with Global => null,
        Post   => To_String'Result'Length = Length (S) and
                  To_String'Result'First = 1;
   --  Converts to an Ada string.

private

   package Char_Vectors is new Ada.Containers.Formal_Indefinite_Vectors
     (Index_Type   => Positive,
      Element_Type => Character,
      Bounded      => False,
      Max_Size_In_Storage_Elements => Character'Size);
   use Char_Vectors;

   type Unbounded_String is new Vector (32);

end Unbounded_Strings;
