------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Types;     use Types;
with Why.Inter; use Why.Inter;

package Gnat2Why.Decls is

   function Is_Mutable_In_Why (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is mutable in
   --  the Why translation

   procedure Translate_Variable
     (File : in out Why_File;
      E    : Entity_Id);
   --  Generate Why declarations that correspond to an Ada top level object
   --  declaration

   procedure Translate_Constant
     (File   : in out Why_File;
      E      : Entity_Id);
   --  Called for IN parameters, named numbers and constant objects

   procedure Translate_Container_Package (Package_Entity : Entity_Id);
   --  Translate a package with a Why3 axiomatization

   procedure Translate_Loop_Entity
     (File : in out Why_File;
      E    : Entity_Id);

end Gnat2Why.Decls;
