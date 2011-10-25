------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - E N U M S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with String_Utils;  use String_Utils;
with Why.Inter;     use Why.Inter;

package Why.Gen.Enums is

   --  This package provides ways to declare enumeration types

   procedure Declare_Ada_Enum_Type
     (File         : W_File_Sections;
      Name         : String;
      Constructors : String_Lists.List);
   --  This creates a new enumeration type with the given name and given
   --  constructor names. It generates the type definition itself, but also
   --  conversions from/to int and the corresponding axioms.
   --  There are two special cases:
   --  * for a type of name "boolean", the function does nothing
   --  * if the list of constructors is empty, no conversion to integers is
   --    generated

end Why.Gen.Enums;
