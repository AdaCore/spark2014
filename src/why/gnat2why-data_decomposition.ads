------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          G N A T 2 W H Y - D A T A _ D E C O M P O S I T I O N           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2023, AdaCore                       --
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

with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Strings.Hash;

package Gnat2Why.Data_Decomposition is

   type Optional_Int (Present : Boolean := False) is record
      case Present is
         when True =>
            Value : Long_Long_Integer;
         when False =>
            null;
      end case;
   end record;

   type Data_Decomposition_Entry is record
      Size        : Optional_Int;
      Value_Size  : Optional_Int;
      Object_Size : Optional_Int;
      Alignment   : Optional_Int;
   end record;

   package String_To_Data_Decomposition_Maps is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => String,
        Element_Type    => Data_Decomposition_Entry,
        Hash            => Ada.Strings.Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   Data_Decomposition_Table : String_To_Data_Decomposition_Maps.Map;

   procedure Read_Data_Decomposition_JSON_File;
   --  Read a data decomposition JSON file and extract relevant information in
   --  global map Data_Decomposition_Table.

end Gnat2Why.Data_Decomposition;
