------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
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

with Atree;             use Atree;
with Common_Containers; use Common_Containers;
with Einfo;             use Einfo;
with Gnat2Why.Util;     use Gnat2Why.Util;
with SPARK_Definition;  use SPARK_Definition;
with Types;             use Types;

package Gnat2Why.Decls is

   procedure Translate_Constant
     (File : W_Section_Id;
      E    : Entity_Id);
   --  Generate a function declaration for IN parameters, named numbers and
   --  constant objects.

   procedure Translate_Constant_Value
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Ekind (E) = E_Constant;
   --  Possibly generate an axiom to define the value of the function
   --  previously declared by a call to Translate_Constant for a constant
   --  object.

   procedure Translate_External_Object (E : Entity_Name);
   --  For a "magic string" generate a dummy declaration module which contains
   --  the type and the variable declaration.

   procedure Translate_External_Object (E : Entity_Id)
   with Pre => (case Ekind (E) is
                   when E_Variable       => not Entity_In_SPARK (E),
                   when E_Abstract_State => True,
                   when others           => False);
   --  Generate Why declarations for an entity E that is only known to proof
   --  as a generated Global of some subprogram. The declaration looks same as
   --  for external objects represented by Entity_Name, just with more precise
   --  tracability comments, e.g. sloc and preserved casing.

   --  The entity is either a variable which is not in SPARK, or an abstract
   --  state which represents its hidden constituents. It is never a constant,
   --  because those in SPARK are translated elsewhere and those not in SPARK
   --  do not appear in Global for they are considered as without variable
   --  input. Other objects, e.g. parameters or loop variables, can only appear
   --  in Global contract of subprograms nested inside their scopes, but if
   --  such an object is not in SPARK then such a nested subprogram is also not
   --  in SPARK (and so it ignored in proof).

   procedure Translate_Loop_Entity
     (File : W_Section_Id;
      E    : Entity_Id);

   procedure Translate_Variable
     (File : W_Section_Id;
      E    : Entity_Id)
   with Pre => Entity_In_SPARK (E);
   --  Generate Why declarations that correspond to an Ada top level object
   --  declaration.

end Gnat2Why.Decls;
