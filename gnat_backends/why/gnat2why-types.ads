------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
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

with Einfo;      use Einfo;
with Namet;      use Namet;
with Types;      use Types;
with Why.Ids;    use Why.Ids;

package Gnat2Why.Types is

   --  This package deals with translations of types.
   --  A single type declaration in Ada is usually translated to a list of
   --  declarations in Why. Depending on the type in Ada, this list contains
   --  at least an abstract type that has the same name as the Ada type, and
   --  several function declarations for conversions (usually to and from
   --  int).
   --
   --  Enumeration types:
   --    We declare an Algebraic data type in Why, along with conversion
   --    from/to int with conversion axioms
   --
   --  Integer types:
   --    We declare an abstract type in Why, along with conversion from/to int
   --    + axioms
   --
   --  Subtypes of Integers:
   --    There is nothing special to do for subtypes: we treat them just as
   --    integer types. This means that sometimes we have to insert
   --    conversions when Ada coerces automatically.
   --
   --  Array types:
   --   We first declare an abstract type for the index type, just as we do
   --   for integer types. We then declare an abstract type for arrays, and
   --   access/update functions with axioms.

   procedure Why_Type_Decl_of_Full_Type_Decl
      (File       : W_File_Id;
       Ident_Node : Node_Id;
       Def_Node   : Node_Id);
   --  Take an Ada full type declaration and transform it into a Why type
   --  declaration, including conversion functions and axioms.

   procedure Why_Type_Decl_of_Subtype_Decl
      (File       : W_File_Id;
       Ident_Node : Node_Id;
       Sub_Ind    : Node_Id);
   --  Take an Ada subtype declaration and transform it into a Why type
   --  declaration, including conversion functions and axioms.

   function Why_Prog_Type_of_Ada_Type
     (Ty   : Node_Id;
      Kind : Entity_Kind)
      return W_Simple_Value_Type_Id;
   --  Take an Ada Type and transform it into a Why program type
   --  ie add a reference constructor on top
   --  example: Integer => integer ref

   function Type_Of_Array_Index (N : Node_Id) return Name_Id;
   --  Given a type definition for arrays, return the type of the array index

end Gnat2Why.Types;
