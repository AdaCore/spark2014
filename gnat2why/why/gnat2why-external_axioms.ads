------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y - E X T E R N A L _ A X I O M S             --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Atree;                      use Atree;
with Einfo;                      use Einfo;
with SPARK_Util.External_Axioms; use SPARK_Util.External_Axioms;
with Types;                      use Types;

package Gnat2Why.External_Axioms is

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   with Pre => Ekind (Package_Entity) = E_Package
     and then Entity_In_Ext_Axioms (Package_Entity);
   --  Translate a package with a Why3 axiomatization

   procedure Process_External_Entities
     (Package_Entity : Entity_Id;
      Process        : not null access procedure (E : Entity_Id))
   with Pre => Ekind (Package_Entity) = E_Package
     and then Entity_In_Ext_Axioms (Package_Entity);
   --  @param Package_Entity A package with external axioms
   --  Applies Process on all entities declared in Package_Entity.

end Gnat2Why.External_Axioms;
