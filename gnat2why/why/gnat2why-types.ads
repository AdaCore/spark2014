------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

--  Translation of types

--  A single type declaration in Ada is usually translated into a list of
--  declarations in Why, grouped in a Why module. Depending on the type in
--  Ada, this list contains at least an abstract type, and several function
--  declarations for conversions.

--  For all Ada types, we have a Why type which is used to model the Ada type.
--  For all discrete types, this is "int", for all floating point types this
--  is "real", and for all array types (currently up to four dimensions)
--  there is a corresponding Why3 type for each dimension in the
--  "__gnatprove_standard.mlw" file. Record types are a bit different,
--  see below.

--  Each Ada type is modeled by a type definition in Why, plus conversion
--  functions to and from the Why model type. Operations of the type
--  are carried out on the model type, so that each operation involves a
--  conversion. Subtype or type conversions in Ada are dealt with naturally by
--  the conversion functions; converting from discrete type A to discrete type
--  B corresponds to a conversion from A to int, and from int to B.

--  See why-gen-arrays.ads for the encoding of arrays.

--  Records are a bit special because there cannot be a "universal" record
--  type in Why, as e.g. for integer types. Instead, we use Why records which
--  directly correspond to the Ada definition. All operations (i.e. field
--  accesses) are defined on the type itself. To deal with conversions between
--  records, we use the same idea as for the other Ada types. However, the
--  underlying model type now is the root type for each record type. The root
--  type is the one that has been introduced with an explicit "record ... end
--  record" scheme, as opposed to a derived type or subtype.

--  Note that the frontend differentiates between a private type and its
--  completion (two different entities), while gnat2why does not look at
--  private types and goes to the actual type (either the completion, or
--  further up if the completion is a derived type of a private type ...)

--  There is an exception to that rule, namely for private types whose
--  completion is not in SPARK. Such types *are* in SPARK, and in this
--  case gnat2why *only* looks at the private entity.

--  For more details about the different encodings, the packages
--    Why.Gen.Scalars
--    Why.Gen.Records
--    Why.Gen.Arrays
--  are useful.

with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with Gnat2Why.Util;        use Gnat2Why.Util;
with Types;                use Types;
with Why.Ids;              use Why.Ids;

package Gnat2Why.Types is

   procedure Translate_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Is_Type (E);
   --  Generate the Why3 declaration module for the type entity in argument.
   --  This function basically dispatches to the corresponding specific package
   --  in Why.Gen.* (Scalars, Records, or Arrays).

   function Ident_Of_Ada_Type (E : Entity_Id) return W_Name_Id
   with Pre => Is_Type (E);
   --  Transform the type entity in argument to an identifier. This function
   --  works with Boolean, but not with things like Universal_Integer.

   procedure Generate_Type_Completion
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Is_Type (E);
   --  Generate the Why3 completion module for the type entity in argument.
   --  This is useful for user-defined equalities, type predicates, type
   --  invariants, as well as to define the type dynamic invariant representing
   --  the constraints respected by the type, and the default initial
   --  assumption representing the constraints respected by the
   --  default-initialized values of the type.

   procedure Generate_VCs_For_Type
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Is_Type (E);
   --  Generate a module for the VCs associated to a type declaration. We
   --  isolate in this separate module those checks that should be done
   --  independently from the value of variables at the point of declaration.

end Gnat2Why.Types;
