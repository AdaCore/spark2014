------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ U T I L - E X T E R N A L _ A X I O M S         --
--                                                                          --
--                                 B o d y                                  --
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

with Exp_Util;         use Exp_Util;
with Opt;              use Opt;
with Sem_Prag;         use Sem_Prag;
with SPARK_Util.Types; use SPARK_Util.Types;

package body SPARK_Util.External_Axioms is

   --------------------------
   -- Entity_In_Ext_Axioms --
   --------------------------

   function Entity_In_Ext_Axioms (E : Entity_Id) return Boolean is
      Pack : constant Entity_Id :=
        Containing_Package_With_Ext_Axioms (E);

   begin
      if No (Pack) then
         return False;
      end if;

      declare
         Prag : constant Node_Id := SPARK_Pragma (Pack);
      begin
         return Present (Prag)
           and then Get_SPARK_Mode_From_Annotation (Prag) = On;
      end;
   end Entity_In_Ext_Axioms;

   --------------------------------
   -- Is_Ext_Axioms_Discriminant --
   --------------------------------

   function Is_Ext_Axioms_Discriminant (E : Entity_Id) return Boolean is
      Typ : constant Entity_Id :=
        Unique_Defining_Entity (Enclosing_Declaration (E));
   begin
      return Type_Based_On_Ext_Axioms (Etype (Typ));
   end Is_Ext_Axioms_Discriminant;

   ----------------------------
   -- Package_Has_Ext_Axioms --
   ----------------------------

   function Package_Has_Ext_Axioms (E : Entity_Id) return Boolean
     renames Has_Annotate_Pragma_For_External_Axiomatization;

   ------------------------------
   -- Type_Based_On_Ext_Axioms --
   ------------------------------

   function Type_Based_On_Ext_Axioms (E : Entity_Id) return Boolean is
     (Present (Underlying_Ext_Axioms_Type (E)));

   --------------------------------
   -- Underlying_Ext_Axioms_Type --
   --------------------------------

   function Underlying_Ext_Axioms_Type (E : Entity_Id) return Entity_Id is
      Typ : Entity_Id := E;
   begin
      loop
         --  Return Typ if it is a private type defined in a package with
         --  external axiomatization.

         if Is_Private_Type (Typ)
           and then Entity_In_Ext_Axioms (Typ)
         then
            return Typ;
         end if;

         --  If Typ is a nouveau type, there is no possible parent type or base
         --  type from a package with external axiomatization. Return Empty.

         if Is_Nouveau_Type (Typ) then
            return Empty;
         end if;

         --  Otherwise, use Etype to reach to the parent type for a derived
         --  type, or the base type for a subtype.

         Typ := Etype (Typ);
      end loop;
   end Underlying_Ext_Axioms_Type;

end SPARK_Util.External_Axioms;
