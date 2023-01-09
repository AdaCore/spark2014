------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   C E _ P R E T T Y _ P R I N T I N G                    --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2023, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with CE_Values;             use CE_Values;
with VC_Kinds;              use VC_Kinds;

package CE_Pretty_Printing is

   Dont_Display : constant CNT_Unbounded_String :=
     (Str   => To_Unbounded_String ("@not_display"),
      Count => 0,
      Elems => S_String_List.Empty);
   --  Value in a counterexample that should not be displayed

   function Make_CNT_Unbounded_String
     (Str : Unbounded_String;
      Cnt : Natural := 1;
      Els : S_String_List.List := S_String_List.Empty)
      return CNT_Unbounded_String
   with Pre => Cnt >= Natural (Els.Length);
   --  Create a CNT_Unbounded_String. Removes "trivial" counterexamples.

   procedure Print_Value_And_Attributes
     (Name        : Unbounded_String;
      Value       : Value_Type;
      Pretty_Line : in out Cntexample_Elt_Lists.List);
   --  Add the value and its attributes to Attributes

   function Print_Value (Value : Value_Type) return CNT_Unbounded_String;
   --  Return a string for a counterexample value. Attributes are ignored.

end CE_Pretty_Printing;
