------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--             S P A R K _ U T I L - E X T E R N A L _ A X I O M S          --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2016-2020, AdaCore                     --
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

package SPARK_Util.External_Axioms is

   --  Units for which External_Axiomatization is specified have their
   --  translation into Why3 defined manually, so much of the treatments in
   --  gnat2why have to be adopted for the entities defined in such units.
   --  Currently, only the (generic) formal containers in the standard library
   --  are using this mechanism.

   function Entity_In_Ext_Axioms (E : Entity_Id) return Boolean;
   --  @param E any entity
   --  @return True iff E is declared in a package with external axiomatization
   --     with SPARK_Mode => On.

   function Is_Access_To_Ext_Axioms_Discriminant
     (N : Node_Id) return Boolean
   with Pre => Nkind (N) = N_Selected_Component;
   --  @param N selected component node
   --  @return True iff the selector is a discriminant of a type defined in
   --     a package with external axiomatization.

   function Is_Ext_Axioms_Discriminant (E : Entity_Id) return Boolean
   with Pre => Ekind (E) = E_Discriminant;
   --  @param E discriminant
   --  @return True iff E is the discriminant of a type defined in a package
   --     with external axiomatization.

   function Package_Has_Ext_Axioms (E : Entity_Id) return Boolean
   with Pre => Is_Package_Or_Generic_Package (E);
   --  @param E (possibly generic) package
   --  @return True iff E is a package with external axiomatization

   function Type_Based_On_Ext_Axioms (E : Entity_Id) return Boolean;
   --  @param E type
   --  @return True iff E is a private type defined in a package with external
   --     axiomatization, or a subtype/derived type from such a type.

   function Underlying_Ext_Axioms_Type (E : Entity_Id) return Entity_Id;
   --  @param E type
   --  @return if E is a private type defined in a package with external
   --     axiomatization, or a subtype/derived type from such a type, return
   --     that type, otherwise Empty.

end SPARK_Util.External_Axioms;
