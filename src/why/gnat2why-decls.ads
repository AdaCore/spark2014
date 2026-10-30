------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with Common_Containers;    use Common_Containers;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Definition;     use SPARK_Definition;
with SPARK_Util;           use SPARK_Util;

package Gnat2Why.Decls is
   --  Declare object symbols and value axioms in contextual modules.
   --  Why.Gen.Binders selects object layouts. Gnat2Why.Expr checks the
   --  expressions in declarations and establishes values at elaboration.

   procedure Translate_Constant (E : Object_Kind_Id)
   with
     Pre =>
       Ekind (E)
       in E_Constant | E_Discriminant | E_In_Parameter | E_In_Out_Parameter
       or else Is_Quantified_Loop_Param (E);
   --  Declare an immutable object's value as a parameterless logic function
   --  available in program expressions, together with its validity flag when
   --  needed. Translate_Constant_Value supplies defining axioms separately.

   procedure Translate_Constant_Value (E : E_Constant_Id);
   --  Generate defining axioms for the value and any validity flag declared
   --  by Translate_Constant, when suitable logical translations are
   --  available. Imported overlays use their unchecked-conversion model.
   --
   --  Add_Axiom_Imports in Why.Inter controls where these axioms can be used.

   procedure Translate_External_Object (E : Entity_Name);
   --  Declare a __private reference for an object E known to proof only
   --  through the explicit or generated Global effects of a subprogram.
   --  Its identity is needed in reads and writes; its value is not modeled.
   --
   --  E is either a variable outside SPARK or an abstract state representing
   --  hidden constituents. Constants in SPARK are translated elsewhere.
   --  Constants outside SPARK are treated as having no variable input and do
   --  not appear in Global contracts. Parameters and loop variables can only
   --  appear in Global contracts of nested subprograms. If such an object is
   --  outside SPARK, those subprograms are also outside SPARK and ignored in
   --  proof.

   procedure Translate_Loop_Entity (E : E_Loop_Id);

   procedure Translate_Variable (E : Object_Kind_Id)
   with Pre => Entity_In_SPARK (E);
   --  Declare the parts of an object mutable in Why3, including fixed parts
   --  of split layouts, initialization and validity flags, move trees, and
   --  predicted end-of-borrow values when needed. For overlays, mutable parts
   --  are functions of the ultimate overlaid object instead of references.

   procedure Translate_Exceptions;
   --  Generate a Why3 module for all the visible exceptions

end Gnat2Why.Decls;
