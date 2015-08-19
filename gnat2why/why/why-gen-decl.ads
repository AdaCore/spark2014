------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Why.Ids; use Why.Ids;

package Why.Gen.Decl is
   --  This package contains all subprograms that are used to build Why
   --  toplevel declarations.

   function New_Type_Decl (Name : String) return W_Declaration_Id;

   function New_Type_Decl
     (Name  : W_Name_Id;
      Alias : W_Type_Id) return W_Declaration_Id;

   function New_Havoc_Declaration (Name : W_Name_Id) return W_Declaration_Id;
   --  @param  Name name of the type for which we want a havoc function
   --  @return Definition of a val havocing its only argument of type name__ref

   function New_Ref_Type_Definition (Name : W_Name_Id) return W_Declaration_Id;
   --  @param  Name name of the type for which we want a reference
   --  @return Definition of a record type with one mutable field of type Name

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl : W_Declaration_Id);

   procedure Emit_Projection_Metas
     (Theory : W_Theory_Declaration_Id;
      Projection_Fun : String);
   --  Emit meta that marks a function as a projection function and disables
   --  inlining of this function in Why3.
   --  @param Theory the theory where the projection meta will be emitted.
   --  @param Projection_Fun the name of the function that will be marked as
   --      projection.

   procedure Emit_Record_Projection_Declaration
     (Theory           : W_Theory_Declaration_Id;
      Param_Ty_Name    : W_Name_Id;
      Return_Ty        : W_Type_Id;
      Field_Id         : W_Identifier_Id;
      SPARK_Field_Name : String := "");
   --  Emit declaration of a projection for a Why3 record type. The projection
   --  projects values of the record type to given field of this type.
   --  The declaration consists of a declaration  of a function that returns a
   --  value of a field Field_Id of a value of the type Param_Ty_Name and
   --  declaration projection metas (see Emit_Projection_Metas).
   --  @param Theory the theory where the projection declaration will be
   --      emitted.
   --  @param Param_Ty_Name the name of the record type being projected.
   --  @param Return_Ty the type to that the record is projected (the type of
   --      the field to that the record is projected).
   --  @param Field_Id the identifier of the field to that the record is
   --      projected.
   --  @param SPARK_Field_Name if the projection projects SPARK record to the
   --      SPARK field, the SPARK name of the field, "" otherwise.
   --      The string "." & SPARK_Field_Name will be appended to the name of
   --      the variable that is being projected. If SPARK_Field_Name equals to
   --      "", nothing will be appended to the name of the variable.

end Why.Gen.Decl;
