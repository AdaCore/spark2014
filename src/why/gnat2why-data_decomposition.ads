------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          G N A T 2 W H Y - D A T A _ D E C O M P O S I T I O N           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2023-2025, AdaCore                     --
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

with Ada.Strings.Hash;
with Snames; use Snames;
with Types;  use Types;
with Uintp;  use Uintp;

package Gnat2Why.Data_Decomposition is

   subtype Size_Attribute_Id is Attribute_Id with
     Static_Predicate => Size_Attribute_Id in Attribute_Size
                                            | Attribute_Value_Size
                                            | Attribute_Object_Size;

   subtype Repr_Attribute_Id is Attribute_Id with
     Static_Predicate => Repr_Attribute_Id in Attribute_Alignment
                                            | Size_Attribute_Id;

   function Get_Attribute_Value
     (E       : Entity_Id;
      Attr_Id : Repr_Attribute_Id) return Uint;
   --  Return the value of E'Attr_Id or No_Uint if not known

   procedure Read_Data_Decomposition_JSON_File;
   --  Read a data decomposition JSON file and extract relevant information in
   --  global map Data_Decomposition_Table.

end Gnat2Why.Data_Decomposition;
