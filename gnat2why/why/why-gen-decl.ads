------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Why.Ids;               use Why.Ids;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Gnat2Why.Util;         use Gnat2Why.Util;

package Why.Gen.Decl is
   --  This package contains all subprograms that are used to build Why
   --  toplevel declarations.

   function New_Type_Decl (Name : String) return W_Declaration_Id;
   --  @param  Name name of the new type
   --  @return Declaration of an abstract logic type named Name

   function New_Type_Decl
     (Name  : W_Name_Id;
      Alias : W_Type_Id) return W_Declaration_Id;
   --  @param  Name name of the new type
   --  @param  Alias type that we want to copy
   --  @return Declaration of a logic type named Name which is transparently
   --      equal to Alias.

   function New_Havoc_Declaration (Name : W_Name_Id) return W_Declaration_Id;
   --  @param  Name name of the type for which we want a havoc function
   --  @return Definition of a val havocing its only argument of type name__ref

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl   : W_Declaration_Id);
   --  Append Decl to the list of declarations from Theory
   --  @param Theory the theory where the declaration will be emitted
   --  @param Decl declaration to emit

   procedure Emit
     (S    : W_Section_Id;
      Decl : W_Declaration_Id);
   --  Append Decl to the list of declarations from the current theory in S
   --  @param S section of the Why file where the declaration will be emitted
   --  @param Decl declaration to emit

   procedure Emit_Projection_Metas
     (Section        : W_Section_Id;
      Projection_Fun : String);
   --  Emit metas that mark a function as a projection function and disables
   --  inlining of this function in Why3.
   --  @param Section section of the Why file where the declaration will be
   --      emitted.
   --  @param Projection_Fun the name of the function that will be marked as
   --      projection.

   procedure Emit_Record_Declaration
     (Section      : W_Section_Id;
      Name         : W_Name_Id;
      Binders      : Binder_Array;
      SPARK_Record : Boolean := False);
   --  Emit declaration of a Why3 record type and counterexample projections
   --  for this record type. The projections project values of the record type
   --  to  fields of this type.
   --  @param Theory the theory where the record declaration will be emitted.
   --  @param Name the name of the record type.
   --  @param Binders the fields of the record type.
   --  @param SPARK_Record if equal to True, it will be assumed that the
   --      generated record type corresponds to SPARK record type. That is, the
   --      Binders correspond to fields of SPARK record type.
   --      In that case, generated projections from this record type to fields
   --      of this record type will append the string "." and the SPARK source
   --      name of the field to the variable being projected.

   procedure Emit_Ref_Type_Definition
     (File : W_Section_Id;
      Name : W_Name_Id);
   --  Emit definition of a record type with one mutable field of type Name and
   --  counterexample projection from this type to this field.
   --  For more information about counterexample projections see documentation
   --  of Emit_Record_Declaration.
   --  @param  Theory the theory where the reference type will be emitted
   --  @param  Name name of the type for which we want a reference

end Why.Gen.Decl;
