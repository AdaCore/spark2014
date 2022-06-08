------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                                N A M E S                                 --
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

--  This is a name table that maps strings to name_id and can recover the
--  original string.

--  Abstract state disabled due to P413-012

package Names with
   SPARK_Mode,
   Annotate          => (GNATprove, Always_Return),
   Abstract_State    => Name_Table,
   Initializes       => Name_Table,
   Initial_Condition => Invariant
is

   type Name_Id is private;

   No_Name : constant Name_Id;
   --  The empty string.

   function Invariant return Boolean
   with Ghost,
        Global => Name_Table;
   --  Internal invariant for the name table.

   procedure Lookup (S : String;
                     N : out Name_Id)
   with Global => (In_Out => Name_Table),
        Pre    => Invariant,
        Post   => Invariant;
   --  Obtain name_id for the given string.

   function To_String (N : Name_Id) return String
   with Global => Name_Table,
        Pre    => Invariant;
   --  The original string.

private

   type Name_Id is new Natural;

   No_Name : constant Name_Id := Name_Id'First;

end Names;
