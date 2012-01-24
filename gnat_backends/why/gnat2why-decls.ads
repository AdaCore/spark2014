------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - D E C L S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

   function Get_Expression_Function (E : Entity_Id) return Node_Id;
   --  If E is the entity of an expression function, return the corresponding
   --  N_Expression_Function original node. Otherwise, return Empty.

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id;
   --  Return the N_Subprogram_Body node for a unique entity E

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id;
   --  Return the N_Specification node for a unique entity E

   function Is_Mutable (N : Node_Id) return Boolean;
   --  Given an N_Defining_Identifier, decide if the variable is mutable in
   --  the Why translation

   procedure Translate_Variable
     (File : W_File_Id;
      E    : Entity_Id);
   --  Generate Why declarations that correspond to an Ada top level object
   --  declaration

   procedure Translate_Constant
     (File : W_File_Id;
      E    : Entity_Id);
   --  Called for IN parameters, named numbers and constant objects

end Gnat2Why.Decls;
