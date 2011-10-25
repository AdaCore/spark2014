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
with Why.Ids;   use Why.Ids;
with Why.Inter; use Why.Inter;

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

   procedure Why_Type_Decl_Of_Entity
      (File       : W_File_Sections;
       Ident_Node : Node_Id);
   --  Take an Ada Entity and consider it as a full type declaration.
   --  Transform it into a Why type declaration, including conversion
   --  functions and axioms.

   procedure Why_Type_Decl_Of_Entity
      (File       : W_File_Sections;
       Name_Str   : String;
       Ident_Node : Node_Id);
   --  Similar to the previous function, but use Name_Str as name of the type,
   --  regardless of the name of the Entity.

   function Why_Prog_Type_Of_Ada_Obj
     (N            : Node_Id;
      Is_Primitive : Boolean := False)
      return W_Simple_Value_Type_Id;
   --  Take an Ada Node and transform it into a Why program type. The Ada Node
   --  is expected to be a Defining_Identifier for a program variable. If
   --  Is_Primitive is True, force the result to be a primitive type
   --  (i.e. no ref).

   function Why_Logic_Type_Of_Ada_Obj (N : Node_Id)
     return W_Primitive_Type_Id;
   --  Take an Ada Node and transform it into a Why logic type. The Ada Node
   --  is expected to be a Defining_Identifier for a program variable.

   function Why_Logic_Type_Of_Ada_Type (Ty : Node_Id)
     return W_Primitive_Type_Id;
   --  Take an Ada Node and transform it into a Why logic type. The Ada Node
   --  is expected to be a Defining_Identifier for a type.

   function Why_Prog_Type_Of_Ada_Type (Ty : Node_Id; Is_Mutable : Boolean)
      return W_Simple_Value_Type_Id;
   --  Take an Ada Node and transform it into a Why program type. The Ada Node
   --  is expected to be a Defining_Identifier for a type. The Boolean
   --  argument decides if a "ref" constructor is built on top.

end Gnat2Why.Types;
