------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - T Y P E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Why.Ids; use Why.Ids;

package Why.Gen.Types is
   --  This package provides ways to create Why types
   package String_Lists is new
      Ada.Containers.Indefinite_Doubly_Linked_Lists (String);

   function New_Abstract_Type (Name : String) return W_Abstract_Type_Id;
   --  Create an abstract type identifier with name Name

   function Declare_Abstract_Type (Name : String) return W_Type_Id;
   --  Create the declaration of an abstract type whose name is Name

   function Declare_Enum_Type (
      Name         : String;
      Constructors : String_Lists.List) return W_Type_Id;
   --  Create the declaration of an enumeration type with name [Name] and list
   --  of constructors [Constructors]. The constructors do not have arguments.

end Why.Gen.Types;
