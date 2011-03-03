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

with Types;        use Types;
with Why.Ids;      use Why.Ids;
with String_Utils; use String_Utils;

package Why.Gen.Types is

   type Why_Type_Enum is (Why_Int, Why_Abstract);
   type Why_Type (Kind : Why_Type_Enum := Why_Int) is
      record
         case Kind is
            when Why_Int =>
               null;
            when Why_Abstract =>
               Wh_Abstract : Node_Id;
         end case;
      end record;

   --  The type of Why types, as used by the translation process; A type in
   --  Why is either the builtin "int" type or a node that corresponds to a
   --  N_Defining_Identifier of an Ada type

   --  This package provides ways to create Why types

   procedure New_Enum_Type_Declaration
     (File         : W_File_Id;
      Name         : String;
      Constructors : String_Lists.List);
   --  Create the declaration of an enumeration type with name [Name] and list
   --  of constructors [Constructors]. The constructors do not have arguments.
   --  In the case of an empty constructor list, generate an abstract type.

end Why.Gen.Types;
