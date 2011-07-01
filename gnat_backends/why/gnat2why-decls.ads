------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - D E C L S                            --
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

with Types;   use Types;
with Why.Ids; use Why.Ids;
package Gnat2Why.Decls is

   function Full_Name (N : Node_Id) return String;
   --  Given an N_Defining_Identifier, return its Full Name, as used in Why.

   function Is_Local_Lifted (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is local or
   --  global

   function Is_Mutable (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is mutable in
   --  the Why translation

   procedure Why_Decl_Of_Ada_Object_Decl
     (File : W_File_Id;
      Id  : Entity_Id;
      Def  : Node_Id := Empty);
   --  Generate Why declarations that correspond to an Ada top level object
   --  declaration
end Gnat2Why.Decls;
